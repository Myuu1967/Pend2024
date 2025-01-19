//=========================================================
// File Name: Pend_2024.c
// MPU board: Raspberry Pi Pico
// Accelerometer + Gyro sensor: MPU6050
// UART Device   : AE-CH340E-TYPEC(Akizuki)
// Rotary Encoder: EC202A100A(Iwatsu Manufacturing)
// Motor Driver  : BD6212HFP(Rohm Semiconductor)
// GPIO Devices  : 3 LEDs, 2 tactile switches
// A/D Converter is used (on Raspberry Pi Pico)
// Motor Current Sensor : AE-ACS712(AKIZUKI)
// 
// On 3rd August 2024 written by @Tanuki_Bayashin
// 
// This Program is to Control the Inverted Pendulum System.
// version 1.0 (as a Pend_2024.c)
//
// New virsion of bigPend.c. (witten on 27th June 2023)
// 
// On Aug. 22th 2024 redesigned the printed circuit board
// as add FIN, RIN of left motordriver and separate the
// power part and control part of the pcb area.
//=========================================================

#include <stdio.h>
#include <string.h>
#include <math.h>
#include <stdlib.h>
#include "pico/stdlib.h"
#include "hardware/uart.h"

#include "pico/binary_info.h"
#include "hardware/gpio.h"
#include "hardware/pwm.h"
#include "hardware/adc.h"
#include "hardware/i2c.h"
#include "hardware/timer.h"
#include "hardware/sync.h"

//=========================================================
// Port Setting
// DigitalOut;
// I2C i2c(PB_9, PB_8);   //Gyro + Accelerometer (SDA, SCLK)
// Serial uart_usb(USBTX, USBRX); //UART (over USB)
//=========================================================

#define UART_ID uart1
#define BAUD_RATE 115200 // 115200 / 8[bit] / (1/0.01[sec]) = 144 characters

#define UART_TX_PIN 8    //(GPIO8 #11)
#define UART_RX_PIN 9    //(GPIO9 #12)
#define PI 3.1415926
#define ONE_G 16383  // 2^14 - 1 = 16383

// for Motor Driver IC (TA7291A TOSHIBA)
#define MotorR_FIN 12 //(GPIO12 #16Pin)  PWM_A[6]
#define MotorR_RIN 13 //(GPIO13 #17Pin)  PWM_B[6]
#define MotorL_FIN 14 //(GPIO14 #19Pin)  PWM_A[7]
#define MotorL_RIN 15 //(GPIO15 #20Pin)  PWM_B[7]

// PWM Modules
//#define PIN_PWM0 12 //(GPIO12 #16Pin PWM_A[6]) unused(2023/07/17)

// detect rotary encorder pulse
#define rotary_encorder_phaseA 16 // GP16(#21 Pin)
#define rotary_encorder_phaseB 17 // GP17(#22 Pin)

#define BUTTON_BLACK 18     // 黒のタクトsw Push -> ON
#define BUTTON_BLUE 19      // 黄色のタクトsw Push -> ON
#define LED_YELLOW 20       // YELLOW LED
#define LED_BLUE 21         // BLUE LED
#define LED_RED 22          // RED LED
#define LED_25 25           // LED_25

//=========================================================
//Accelerometer and gyro offset
//=========================================================
// variables for calculate offset
// for offset of accelaration
float acc_Y_offset = 0.0;
float acc_Z_offset = 0.0;
// for offset of angular velocity
float gyro_X_offset = 0.0;

//=========================================================
//Accelerometer and gyro statistical data
//=========================================================
// By default these devices are on bus address 0x68
static int addr = 0x68;

int16_t acceleration[3], gyro[3];
int16_t* temperature;
int sample_num = 1000;

int cnt_P_angle = 0, cnt_P_angle_dot = 0;
float P_angle, P_angle_dot, P_angle_ave, P_angle_dot_ave;
float P_angle_value, P_angle_dot_value;
float P_angle_data[20];
float P_angle_dot_data[20];

//=========================================================
//Rotary encoder variables
//=========================================================
int rotary_encoder_update_rate = 25; //usec
int rotary_encoder_resolution = 100;
int phaseA, phaseB;
int code = 0;
int table[16] = { 0, 1, -1, 0,  -1, 0, 0, 1,  1, 0, 0, -1,  0, -1, 1, 0 };

int encoder_value = 0;

int cnt_W_angle = 0, cnt_W_angle_dot = 0;
float W_angle, W_angle_ave, W_angle_dot, W_angle_dot_ave;
float W_angle_value, W_angle_dot_value;
float W_angle_data[20];
float W_angle_dot_data[20];

//=========================================================
// PWM to Mortor Voltage
// DATA from a experiment
//=========================================================
int Motor_Mode = 0; // モーターが正転(2)か逆転(1)かSTOP(0)か
int Motor_Flag = 1; // Motor_Flag: 0 -> pwm_value must be 0 (未使用)
uint pwm1_slice_num, pwm2_slice_num, pwm3_slice_num, pwm4_slice_num;

float volts;
int pwm_value = 0, pwm_value2 = 0;
const float balance = -6.5;

//=========================================================
// PWM to Mortor Voltage
// DATAs from a experiment
//=========================================================
//feed back gain
//(R=1000, Q = diag(1, 1, 10, 10), f=100Hz)
float K[4] = { 120.0, 60.0, 0.0, 0.0};  // Gain of Mr.Beppu
float Kp = 1.2, Kd = 0.15;
float K_w = 0.8;
float deg2rad = 3.141593 / 180.0;
float rad2deg = 180.0 / 3.141593;
float W_angle_dot_ref = 0.0;
float ratio = 1.0;

static uint32_t count_encoder = 0, count_control = 0;
int cnt_main, cnt_uart;

//=========================================================
//Motor control variables
float feedback_rate = 0.01; //sec
struct repeating_timer timer_encorder;
struct repeating_timer timer_control;
struct repeating_timer timer_standing;
bool cancelled_encorder;
bool cancelled_control;
bool cancelled_standing;

static uint32_t t_start = 0, t_end = 0, t_end2 = 0;
static uint32_t t_start_control, t_end_control;
static uint32_t start_main;

bool control_ready = false;

//=========================================================
// Accelerometer (MPU6050)
// Gyroscope
//========================================================= 
//
#ifdef i2c_default
static void mpu6050_reset() {
    // Two byte reset. First byte register, second byte data
    // There are a load more options to set up the device in different ways that could be added here
    uint8_t buf[] = { 0x6B, 0x00 };
    i2c_write_blocking(i2c_default, addr, buf, 2, false);

    // set P_angle_dot ±500[degree/sec]
    buf[0] = 0x1B;
    buf[1] = 0x08;  // 0x01 => 0x08 changed(2022/08/11)
    i2c_write_blocking(i2c_default, addr, buf, 2, false);

    // set accelaration ±2G 
    buf[0] = 0x1C;
    buf[1] = 0x00;
    i2c_write_blocking(i2c_default, addr, buf, 2, false);

    // set LPF BW 260Hz(0.0ms delay) for Accel,
    // 256Hz(0.98ms delay) for Gyro
    buf[0] = 0x1A;
    buf[1] = 0x00;
    i2c_write_blocking(i2c_default, addr, buf, 2, false);

}

float get_P_angle() {

    uint8_t buffer[6];
    float sum;
    float x, y;

    // Start reading acceleration registers from register 0x3B for 6 bytes
    uint8_t val = 0x3B;
    // true to keep master control of bus
    i2c_write_blocking(i2c_default, addr, &val, 1, true);
    i2c_read_blocking(i2c_default, addr, buffer, 6, false);

    acceleration[0] = (buffer[0] << 8) | buffer[1];
    acceleration[1] = (buffer[2] << 8) | buffer[3];
    acceleration[2] = (buffer[4] << 8) | buffer[5];

    // 86.03 is the value of compensation for initial posture
    x = (float)acceleration[1] - acc_Y_offset;
    y = (float)acceleration[2] - acc_Z_offset;

    P_angle = (float)atan2((double)y, (double)x) * 180.0 / PI;
    //P_angle = 90.0;

    if ((P_angle > 500.0) || (P_angle < -500.0)) {
        P_angle = P_angle_data[0] * 15.0;
    }

    //ave_value[i] -= ave_data[i][p]
    //ave_data[i][p] = fiveData[i + 1][j] / 10.0
    //ave_value[i] += ave_data[i][p]
    //ave_result[i][j] = ave_value[i]

    cnt_P_angle = (cnt_P_angle + 1) % 15;
    P_angle_value -= P_angle_data[cnt_P_angle];
    P_angle_data[cnt_P_angle] = P_angle / 15.0; // 過去10点の平均
    P_angle_value += P_angle_data[cnt_P_angle];
    P_angle_ave = P_angle_value;

    return P_angle; // [degree]

}

float get_P_angle_dot() {

    uint8_t buffer[2];
    float sum;

    // Now gyro data from reg 0x43 for 6 bytes
    uint8_t val = 0x43;
    i2c_write_blocking(i2c_default, addr, &val, 1, true);
    i2c_read_blocking(i2c_default, addr, buffer, 2, false);  // False - finished with bus

    gyro[0] = (buffer[0] << 8) | buffer[1];

    // 2^15 - 1 = 32767, ±500 [degree/s] for Full range
    // -500を掛けているのは座標系を合わせるため
    P_angle_dot = (gyro[0] - gyro_X_offset) * (-500.0) / 32767.0; // [degree/s]

    if ((P_angle_dot > 500.0) || (P_angle_dot < -500.0)) {
        P_angle_dot = P_angle_dot_data[0] * 15.0;
    }

    cnt_P_angle_dot = (cnt_P_angle_dot + 1) % 15;
    P_angle_dot_value -= P_angle_dot_data[cnt_P_angle_dot];
    P_angle_dot_data[cnt_P_angle_dot] = P_angle_dot / 15.0; // 過去10点の平均
    P_angle_dot_value += P_angle_dot_data[cnt_P_angle_dot];
    P_angle_dot_ave = P_angle_dot_value;

    return P_angle_dot;  // [degree/sec]
}

#endif

void Calibration() {

    //// Calculate these variables
    // acc_Y_offset;
    // acc_Z_offset;
    // gyro_X_offset;

    float acc_Y_sum = 0.0;
    float acc_Z_sum = 0.0;
    float gyro_X_sum = 0.0;
    float ONE_G_sin, ONE_G_cos, P_angle_0;

//    P_angle_0 = 53.2; // 2023/07/29 measured
    P_angle_0 = 90.0; // 2023/07/29 measured
    ONE_G_sin = ONE_G * sin(P_angle_0 * PI / 180.0);
    ONE_G_cos = ONE_G * cos(P_angle_0 * PI / 180.0);
    ///////////////////////////////////////////////
    // Calculate offset of acc and gyro raw data //
    // sample_num = 500                          //
    ///////////////////////////////////////////////
    for (int i = 0; i < sample_num; i++) {
        P_angle = get_P_angle();
        P_angle_dot = get_P_angle_dot();

        // #define ONE_G 16383 = 2^14 - 1
        acc_Y_sum += acceleration[1] - ONE_G_cos;
        acc_Z_sum += acceleration[2] - ONE_G_sin;
        gyro_X_sum += gyro[0];

        // delay 500[μs]
        sleep_ms(1);
    }

    // results of calculation of mean values
    acc_Y_offset = acc_Y_sum / sample_num;
    acc_Z_offset = acc_Z_sum / sample_num;
    gyro_X_offset = gyro_X_sum / sample_num;

    return;
}

//=========================================================
//Rotary encoder polling function
// under 1usec process time (Raspberry Pi Pico 125MHz)
//=========================================================
int read_encoder() {

    phaseA = gpio_get(rotary_encorder_phaseA);
    phaseB = gpio_get(rotary_encorder_phaseB);

    return (phaseB << 1) + phaseA;

}

bool rotary_encoder_check(struct repeating_timer* t)
{
    // 割り込みを無効化
    uint32_t interrupt_status_encorder = save_and_disable_interrupts();

    //t_start = time_us_32();

    int temp;

    temp = read_encoder();
    //check the movement
    code = ((code << 2) + temp) & 0xf;
    //update the encoder value
    int value = 1 * table[code];

    encoder_value += value;

    //encoder_value = 0;
    //t_end = time_us_32() - t_start;
    //count_encoder++;

    // 割り込みを再度有効化
    restore_interrupts(interrupt_status_encorder);

    return true;
}

float get_W_angle()  // angular of wheels
{
    // calculate W_angle [degree]
    W_angle = (float)encoder_value * (-0.9);

    if ((W_angle > 100000.0) || (W_angle < -100000.0)) {
        W_angle = W_angle_data[0];
    }

    W_angle_data[0] = W_angle;
    for (int i = 0; i < 14; i++) {
        W_angle_data[14 - i] = W_angle_data[13 - i];
    }

    float sum = 0.0;
    for (int i = 0; i < 15; i++) {
        sum += W_angle_data[i];
    }
    W_angle_ave = sum / 15.0;

    return W_angle;  // [degree]
}

float get_W_angle_dot()  // angular of wheels
{
    // calculate W_angle_dot [degree / s]
    W_angle_dot = (W_angle_data[0] - W_angle_data[5]) / 0.05; // 90ms --> 50ms(2023/07/23)

    if ((W_angle_dot > 20000.0) || (W_angle_dot < -20000.0)) {
        W_angle_dot = W_angle_dot_data[0];
    }
    
    W_angle_dot_data[0] = W_angle_dot;
    for (int i = 0; i < 14; i++) {
        W_angle_dot_data[14 - i] = W_angle_dot_data[13 - i];
    }

    float sum = 0.0;
    for (int i = 0; i < 15; i++) {
        sum += W_angle_dot_data[i];
    }
    W_angle_dot_ave = sum / 15.0;

    return W_angle_dot; //[degree/sec]
}

//=========================================================
// calcurate the input voltage of the motor for 
// inverted pendulum.
// (2022/12/17)
//=========================================================
bool Control_Pendulum(struct repeating_timer* t)
{    
    
    //about 400usec passed for this process

    // 割り込みを無効化
    uint32_t interrupt_status_control = save_and_disable_interrupts();

    t_start_control = time_us_32();

    P_angle     = get_P_angle();
    P_angle_dot = get_P_angle_dot();
    //W_angle     = get_W_angle();
    //W_angle_dot = get_W_angle_dot();

    //reset
    volts = 0.0;

    volts = (-1.0) * (K[0] * (P_angle_ave - balance) + K[1] * P_angle_dot_ave) * deg2rad;
    //    + K[2] * W_angle_ave + K[3] * W_angle_dot_ave) * deg2rad;


    //volts = K_w * (W_angle_dot_ave - W_angle_dot_ref) * PI / 180.0;
    //volts = ( Kp * (W_angle_ave - 90.0 + P_angle_ave) + Kd * W_angle_dot_ave) * deg2rad;

    if (volts > 0) {
        Motor_Mode = 1;    // CCW
    }
    else if (volts < 0) {
        Motor_Mode = 2;    // CW
        volts = volts * (-1.0);
    }
    else {
        Motor_Mode = 0;    // STOP
    }

    /*if (volts > 4.0) {
        volts = 4.0;
    }
    */

    //calculate PWM pulse width
    pwm_value = (int)(volts * 204.8 + 80.0);
    pwm_value2 = (int)(volts * 204.8 + 80.0);
    if (pwm_value > 1023) {  // MAX: 1023
        pwm_value = 1023;
    }
    if (pwm_value2 > 1023) {  // MAX: 1023
        pwm_value2 = 1023;
    }

/*    if ((P_angle_ave - balance > 45.0) || (P_angle_ave - balance < -45.0)) {
        pwm_value = 0;
    }
 */

    //drive the motor
    if (Motor_Mode == 1) { // CCW
        //forward
        gpio_put(LED_BLUE, 1);  // LED_BLUE ON
        gpio_put(LED_RED, 0);
        // CCW
        pwm_set_chan_level(pwm1_slice_num, PWM_CHAN_A, pwm_value);
        pwm_set_chan_level(pwm2_slice_num, PWM_CHAN_B, 0);

        pwm_set_chan_level(pwm3_slice_num, PWM_CHAN_A, pwm_value2);
        pwm_set_chan_level(pwm4_slice_num, PWM_CHAN_B, 0);
    }
    //drive the motor in reverse
    else if (Motor_Mode == 2) {
        //backward
        gpio_put(LED_BLUE, 0);  // LED_RED ON
        gpio_put(LED_RED, 1);
        // CW
        pwm_set_chan_level(pwm1_slice_num, PWM_CHAN_A, 0);
        pwm_set_chan_level(pwm2_slice_num, PWM_CHAN_B, pwm_value);

        pwm_set_chan_level(pwm3_slice_num, PWM_CHAN_A, 0);
        pwm_set_chan_level(pwm4_slice_num, PWM_CHAN_B, pwm_value2);
    }
    else {
        //stop
        gpio_put(LED_BLUE, 0);  // LEDs OFF
        gpio_put(LED_RED, 0);
        //
        pwm_set_chan_level(pwm1_slice_num, PWM_CHAN_A, 1023);
        pwm_set_chan_level(pwm2_slice_num, PWM_CHAN_B, 1023);
        pwm_set_chan_level(pwm3_slice_num, PWM_CHAN_A, 1023);
        pwm_set_chan_level(pwm4_slice_num, PWM_CHAN_B, 1023);
    }


    //pwm_set_chan_level(pwm1_slice_num, PWM_CHAN_A, pwm_value);
    //pwm_set_chan_level(pwm2_slice_num, PWM_CHAN_B, 0);
    //pwm_set_chan_level(pwm3_slice_num, PWM_CHAN_A, 0);
    //pwm_set_chan_level(pwm4_slice_num, PWM_CHAN_B, pwm_value);

    cnt_main = (cnt_main + 1) % 100;
    if (cnt_main >= 50) {
        gpio_put(LED_25, 1); // LED_25 is ON
    }
    else {
        gpio_put(LED_25, 0); // LED_25 is OFF
    }

    t_end_control = time_us_32() - t_start_control;
//    count_control++;

    // 割り込みを再度有効化
    restore_interrupts(interrupt_status_control);

    return true;
}

void send_a_3times() {
    sleep_ms(100);

    uart_puts(UART_ID, "a\n"); // 1st send
    sleep_ms(1);

    gpio_put(LED_RED, 1); // RED LED is ON
    sleep_ms(499);
    gpio_put(LED_RED, 0); // RED LED is OFF
    sleep_ms(500);

    uart_puts(UART_ID, "a\n"); // 2nd send
    sleep_ms(1);

    gpio_put(LED_RED, 1); // RED LED is ON
    sleep_ms(499);
    gpio_put(LED_RED, 0); // RED LED is OFF
    sleep_ms(500);

    uart_puts(UART_ID, "a\n"); // 3rd send
    sleep_ms(1);

    gpio_put(LED_RED, 1); // RED LED is ON
    sleep_ms(499);
    gpio_put(LED_RED, 0); // RED LED is OFF
    sleep_ms(500);

    return;
}

// check Pendulum is standing or not.
bool checkStanding(struct repeating_timer* t)
{
    // 割り込みを無効化
    uint32_t interrupt_status_standing = save_and_disable_interrupts();

/*    if (control_ready == false) {
        P_angle = get_P_angle();
    }
 */   
    P_angle = get_P_angle();
    
    if ( (P_angle_ave > balance - 0.5) && (P_angle_ave < balance + 0.5) ) { // 5.8 degree(first value: 2.3 )
        gpio_put(LED_YELLOW, 1); // YELLOW LED is ON
    }
    else {
        gpio_put(LED_YELLOW, 0); // YELLOW LED is OFF
    }

    // 割り込みを再度有効化
    restore_interrupts(interrupt_status_standing);

    return true;
}

int char_to_int(char c) {
    // 文字が '0' から '9' の範囲にあるかチェック
    if (c >= '0' && c <= '9') {
        // 文字を整数に変換
        int num = c - '0';
        // 整数を float に変換
        return num;
    }
    else {
        // エラー処理（必要に応じて変更）
        printf("Error: Input character is not a digit.\n");
        return -1;
    }
}


void receive_string_uart(uart_inst_t* uart, char* buffer, size_t buffer_size) {
    size_t index = 0;
    char ch;

    while (index < buffer_size - 1) { // 1バイトはヌル終端用
        ch = uart_getc(uart); // 1バイトのデータを受信
        if (ch == '\n') {     // 改行文字で終了
            break;
        }
        buffer[index++] = ch;
    }
    buffer[index] = '\0'; // 文字列の終端
}

//=========================================================
// Main
//=========================================================
void main() {

    static char s[100];
    int i, j, count;
    int led_yellow = 0;
    int count_led_yellow = 0;
    float time = 0.025405; //25.405[ms]
    bool start_control = false;
    float adc_factor, motor_volt, motor_current, motor_driver;
    float value;

    /////////////////////////
    // UART 初期設定       //
    /////////////////////////
    // process something important ?
    stdio_init_all();

    // Set up our UART with the required speed.
    uart_init(UART_ID, BAUD_RATE);

    // Set the TX and RX pins by using the function select on the GPIO
    gpio_set_function(UART_TX_PIN, GPIO_FUNC_UART);
    gpio_set_function(UART_RX_PIN, GPIO_FUNC_UART);

    // UART設定
    uart_set_hw_flow(UART_ID, false, false);  // ハードウェアフローコントロールを無効化
    uart_set_format(UART_ID, 8, 1, UART_PARITY_NONE);  // データビット: 8, ストップビット: 1, パリティ: なし

    /////////////////////////////
    // 加速度センサー 初期設定 //
    /////////////////////////////

#if !defined(i2c_default) || !defined(PICO_DEFAULT_I2C_SDA_PIN) || !defined(PICO_DEFAULT_I2C_SCL_PIN)
    #warning i2c / mpu6050_i2c example requires a board with I2C pins
    //uart_puts(UART_ID, "Default I2C pins were not defined");
#else
    //uart_puts(UART_ID, "Hello, MPU6050! Reading raw data from registers...");

    // This example will use I2C0 on the default SDA and SCL pins (4, 5 on a Pico)
    i2c_init(i2c_default, 400 * 1000);
    gpio_set_function(PICO_DEFAULT_I2C_SDA_PIN, GPIO_FUNC_I2C);
    gpio_set_function(PICO_DEFAULT_I2C_SCL_PIN, GPIO_FUNC_I2C);
    gpio_pull_up(PICO_DEFAULT_I2C_SDA_PIN);
    gpio_pull_up(PICO_DEFAULT_I2C_SCL_PIN);

    // Make the I2C pins available to picotool
    bi_decl(bi_2pins_with_func(PICO_DEFAULT_I2C_SDA_PIN, PICO_DEFAULT_I2C_SCL_PIN, GPIO_FUNC_I2C));

    mpu6050_reset();

#endif

    /////////////////////////////////////////
    // GPIO(for LEDs and BUTTONs) initialize
    /////////////////////////////////////////
    gpio_init(LED_RED);
    gpio_init(LED_BLUE);
    gpio_init(LED_YELLOW);
    gpio_init(LED_25);
    gpio_set_dir(LED_RED, GPIO_OUT);
    gpio_set_dir(LED_BLUE, GPIO_OUT);
    gpio_set_dir(LED_YELLOW, GPIO_OUT);
    gpio_set_dir(LED_25, GPIO_OUT);

    gpio_init(BUTTON_BLACK);
    gpio_set_dir(BUTTON_BLACK, GPIO_IN);
    gpio_pull_up(BUTTON_BLACK);

    gpio_init(BUTTON_BLUE);
    gpio_set_dir(BUTTON_BLUE, GPIO_IN);
    gpio_pull_up(BUTTON_BLUE);
    sleep_ms(1);

    ///////////////////////////////////
    // Calibration Start
    ///////////////////////////////////

    sleep_ms(1000);

    gpio_put(LED_YELLOW, 1); // YELLOW LED is ON
    Calibration();

    snprintf(s, sizeof(s), "%5.3f,%5.3f,%5.3f\n", 
                                acc_Y_offset, acc_Z_offset, gyro_X_offset);
    uart_puts(UART_ID, s);
    sleep_ms(100);
    gpio_put(LED_YELLOW, 0); // YELLOW LED is OFF
    sleep_ms(500);

    ///////////////////////////////////////////////
    // checkStanding Process
    // 
    ///////////////////////////////////////////////
    add_repeating_timer_ms(-1, checkStanding, NULL, &timer_standing);
    sleep_ms(1);

    count = 0;
    led_yellow = 0;
    count_led_yellow = 0;
    //gpio_put(LED_YELLOW, 1); // YELLOW LED is ON

    // While start_control is false,this while loop is running.
    // and pushing Yellow Button for 1 second continueously,
    // start_control turned to true and get out from this loop!
    while (start_control == false) {
        if (gpio_get(BUTTON_BLUE) == 0) {
            sleep_ms(1);
            count++;

            gpio_put(LED_BLUE, 1);
            gpio_put(LED_RED, 0);

            if (count > 1000) {
                start_control = true;
                gpio_put(LED_BLUE, 0);
                gpio_put(LED_RED, 0);
                break;
            }
        }
        else {
            count = 0;
            gpio_put(LED_BLUE, 0);
            gpio_put(LED_RED, 1);
        }
    }

    sleep_ms(1);

    // Set the phaseA and phaseB pins to GPIO
    gpio_init(rotary_encorder_phaseA);
    gpio_init(rotary_encorder_phaseB);
    gpio_set_dir(rotary_encorder_phaseA, GPIO_IN);
    gpio_set_dir(rotary_encorder_phaseB, GPIO_IN);

    encoder_value = 0;

    //////////////////////////////////
    // start controlling the machine
    // after send "a" 3 times.
    // YELLOW LED is ON for 3[sec]
    //////////////////////////////////
    send_a_3times();

    /////////////////////////
    // A/D 変換の処理      //
    /////////////////////////  ×（A/D 変換はお休み）
    // ADC module initialize
    adc_init();
    // Make sure GPIO is high-impedance, no pullups etc
    adc_gpio_init(26);
    adc_gpio_init(27);
    adc_gpio_init(28);

    // Select ADC input 0 (GPIO26)
    //adc_select_input(0);

    ///////////////////////////
    // PWM の前処理          //
    // (Motor_IN1, Motor_IN2)//
    ///////////////////////////
    // MotorR_FIN 12 (GPIO12 #16Pin)  PWM_A[6]
    // MotorR_RIN 13 (GPIO13 #17Pin)  PWM_B[6]
    // MotorL_FIN 14 (GPIO14 #19Pin)  PWM_A[7]
    // MotorL_RIN 15 (GPIO15 #20Pin)  PWM_B[7]
    //////////////////////////////////////////////
    /* GPIOにPWMを割り当て */
    gpio_set_function(MotorR_FIN, GPIO_FUNC_PWM);
    gpio_set_function(MotorR_RIN, GPIO_FUNC_PWM);

    pwm1_slice_num = pwm_gpio_to_slice_num(MotorR_FIN);
    pwm2_slice_num = pwm_gpio_to_slice_num(MotorR_RIN);

    /* clkdiv と wrap を指定 */
    pwm_set_clkdiv(pwm1_slice_num, 12.1875);
    pwm_set_wrap(pwm1_slice_num, 1023);

    pwm_set_clkdiv(pwm2_slice_num, 12.1875);
    pwm_set_wrap(pwm2_slice_num, 1023);

    /* レベル値(デューティカウント値)を設定(ここでは0) */
    pwm_set_chan_level(pwm1_slice_num, PWM_CHAN_A, 1023);
    pwm_set_chan_level(pwm2_slice_num, PWM_CHAN_B, 1023);

    /* pwm0 start */
    pwm_set_enabled(pwm1_slice_num, true);
    pwm_set_enabled(pwm2_slice_num, true);

    /* GPIOにPWMを割り当て */
    gpio_set_function(MotorL_FIN, GPIO_FUNC_PWM);
    gpio_set_function(MotorL_RIN, GPIO_FUNC_PWM);

    pwm3_slice_num = pwm_gpio_to_slice_num(MotorL_FIN);
    pwm4_slice_num = pwm_gpio_to_slice_num(MotorL_RIN);

    /* clkdiv と wrap を指定 */
    pwm_set_clkdiv(pwm3_slice_num, 12.1875);
    pwm_set_wrap(pwm3_slice_num, 1023);

    pwm_set_clkdiv(pwm4_slice_num, 12.1875);
    pwm_set_wrap(pwm4_slice_num, 1023);

    /* レベル値(デューティカウント値)を設定(ここでは0) */
    pwm_set_chan_level(pwm3_slice_num, PWM_CHAN_A, 1023);
    pwm_set_chan_level(pwm4_slice_num, PWM_CHAN_B, 1023);

    /* pwm0 start */
    pwm_set_enabled(pwm3_slice_num, true);
    pwm_set_enabled(pwm4_slice_num, true);

    /* END of PWM Module Setting */

    /////////////////////////////////////////////  
    //  Timer
    /////////////////////////////////////////////

    // start rotary encorder process (25 us)
    //add_repeating_timer_us(-25, rotary_encoder_check, NULL, &timer_encorder);
    //sleep_ms(1);

    // calculate P_angle [deg] as initial values
    P_angle_value = get_P_angle();
    P_angle_data[0] = P_angle_value / 15.0;
    for (int i = 1; i < 20; i++) {
        P_angle_data[i] = P_angle_data[0];
    }

    // calculate P_angle_dot [deg/s] as initial values
    P_angle_dot_value = get_P_angle_dot();
    P_angle_dot_data[0] = P_angle_dot_value / 15.0;
    for (int i = 1; i < 20; i++) {
        P_angle_dot_data[i] = P_angle_dot_data[0];
    }

    // calculate W_angle [degree] as initial values
/*    W_angle_value = (float)encoder_value * 0.9; // / 400.0 * 360.0
    W_angle_data[0] = W_angle_value;
    for (int i = 1; i < 20; i++){
        W_angle_data[i] = W_angle_data[0];
    }

    // calculate P_angle_dot [deg/s] as initial values
    W_angle_dot_data[0] = get_W_angle_dot();
    W_angle_value = W_angle_dot_data[0];
    for (int i = 1; i < 20; i++) {
        W_angle_dot_data[i] = W_angle_dot_data[0];
    }  */

    //count_control = 250;
    // start main control process (10.0 ms)
    add_repeating_timer_ms(-10, Control_Pendulum, NULL, &timer_control);
    sleep_ms(1);

    control_ready = true;

    uart_puts(UART_ID, "Start!!\n");
    sleep_ms(1);

    //===========================================
    //Main loop
    //it takes 10 msec (calculation)
    //===========================================
    Motor_Mode = 0;
    count = 0;
    adc_factor = 5.0 / 4096.0;
    cnt_main = 0;
    cnt_uart = 0;
    pwm_value = 0;

    float out1 = 0.0, out2 = 0.0;
    char buffer[10];
    float data = 0.0;
    int index = 0;
    int uart_cnt = 0;
    float result0[500], result1[500], result2[500], result;

    adc_select_input(1);
    result = (float)adc_read();

    for (int i = 0; i < 500; i++) {
        result1[i] = result;
        result2[i] = result;
    }

    start_main = time_us_32();
    while(1)
    {
        //t_start = time_us_32();

        // Select ADC input 0 (GP26)
        //adc_select_input(0);
        //result0 = (uint16_t)adc_read();

        // Select ADC input 1 (GP27)
        /*out1 -= adc_factor * result1[index] * 0.002;

        adc_select_input(1);
        result1[index] = (float)adc_read();

        out1 += adc_factor * result1[index] * 0.002;

        // Select ADC input 2 (GP28)
        out2 -= adc_factor * result2[index] * 0.002;

        adc_select_input(2);
        result2[index] = (float)adc_read();

        out2 += adc_factor * result2[index] * 0.002;

        index = (index + 1) % 500;

        t_end = time_us_32() - t_start;
        */

        //snprintf(s, sizeof(s), "%4d,%4d,%4.3f,%4.3f\n", t_end, t_end_control, W_angle_ave, W_angle_dot_ave);
        //snprintf(s, sizeof(s), "%u,%d,%2.5e\n", t_end, pwm_value, W_angle_dot_ave);
        //uart_puts(UART_ID, s);

        //value = adc_factor * (float)result0;
        //snprintf(s, sizeof(s), "ADC0: %4.3f,\n", value);
        //uart_puts(UART_ID, s);
        t_start = time_us_32();

     //uart_cnt = (uart_cnt + 1) % 10;
     //   if (uart_cnt == 9) {
    /*        if (uart_is_readable(UART_ID)) {
                receive_string_uart(UART_ID, buffer, sizeof(buffer));
                // 一定時間待機
                sleep_us(10);

            }
    */
            // PCにデータを送信
            //data = atof(buffer);
        /*    if (data < 0 || data > 1023) {
                break;
            } */

        /*    P_angle = get_P_angle();
            P_angle_dot = get_P_angle_dot();
            W_angle = get_W_angle();
            W_angle_dot = get_W_angle_dot();
        */
/*          pwm_value = (int)data;
            //pwm_value = 400;
            //K[0] = data;
            double send_time = (double)t_end2;
            snprintf(s, sizeof(s), "P_ang dP and ave:, %lf, %2.4f, %2.4f, %2.4f, %2.4f\n", send_time,
            //    P_angle, P_angle_ave, P_angle_dot, P_angle_dot_ave);
                W_angle, W_angle_ave, W_angle_dot, W_angle_dot_ave);
            uart_puts(UART_ID, s);
*/
    //    }

        //pwm_set_chan_level(pwm1_slice_num, PWM_CHAN_A, pwm_value);
        //pwm_set_chan_level(pwm2_slice_num, PWM_CHAN_B, 0);

        //pwm_set_chan_level(pwm3_slice_num, PWM_CHAN_A, pwm_value);
        //pwm_set_chan_level(pwm4_slice_num, PWM_CHAN_B, 0);

/*        if (gpio_get(BUTTON_BLACK) == 0) { // BUTTON_BLACK ON
            gpio_put(LED_BLUE, 1);  // LED_YELLOW ON
            gpio_put(LED_RED, 0);   // LED_YELLOW ON
        }
        else {                              // BUTTON_BLACK OFF
            gpio_put(LED_BLUE, 0);  // LED_YELLOW OFF
            gpio_put(LED_RED, 1);   // LED_YELLOW ON
        }

        cnt_main = (cnt_main + 1) % 500;
        if (cnt_main >= 250) {
            gpio_put(LED_25, 1); // LED_25 is ON
        }
        else {
            gpio_put(LED_25, 0); // LED_25 is OFF
        }
*/
        sleep_ms(10);

        t_end2 = time_us_32() - t_start;
    }
    //===========================================
    //Main loop (end)
    //=========================================== 

    cancelled_control = cancel_repeating_timer(&timer_control);
    uart_puts(UART_ID, "cancelled... _control");
    snprintf(s, sizeof(s), "%d", cancelled_control);
    uart_puts(UART_ID, s);
    uart_puts(UART_ID, "\0");

    sleep_ms(1);

    cancelled_encorder = cancel_repeating_timer(&timer_encorder);
    uart_puts(UART_ID, "cancelled... _encorder");
    snprintf(s, sizeof(s), "%d", cancelled_encorder);
    uart_puts(UART_ID, s);
    uart_puts(UART_ID, "\0");

    sleep_ms(1);

    cancelled_standing = cancel_repeating_timer(&timer_standing);
    uart_puts(UART_ID, "cancelled... _standing");
    snprintf(s, sizeof(s), "%d", cancelled_standing);
    uart_puts(UART_ID, s);
    uart_puts(UART_ID, "\0");

    sleep_ms(1);

    return;
}
