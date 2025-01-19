add_executable(Pend_2024
        Pend_2024.c
        )

# Pull in our (to be renamed) simple get you started dependencies
target_link_libraries(Pend_2024 pico_stdlib
                             hardware_uart
                             pico_binary_info
                             hardware_gpio
                             hardware_pwm
                             hardware_adc
                             hardware_i2c
                             hardware_timer
                             hardware_sync
                             )

# create map/bin/hex file etc.
pico_add_extra_outputs(Pend_2024)

# add url via pico_set_program_url
example_auto_set_url(Pend_2024)
