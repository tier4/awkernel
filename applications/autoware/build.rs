use std::{env, fs, path::PathBuf};

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR is not set"));
    let csv_data_path = out_dir.join("csv_data.rs");

    let imu_csv = read_csv_from_env("IMU_CSV_PATH");
    let velocity_csv = read_csv_from_env("VELOCITY_CSV_PATH");

    let generated = format!(
        "pub const IMU_CSV_DATA_STR: &str = {imu:?};\npub const VELOCITY_CSV_DATA_STR: &str = {velocity:?};\n",
        imu = imu_csv,
        velocity = velocity_csv,
    );

    fs::write(&csv_data_path, generated).expect("failed to write generated csv constants");
}

fn read_csv_from_env(var_name: &str) -> String {
    let Ok(path) = env::var(var_name) else {
        return String::new();
    };

    match fs::read_to_string(&path) {
        Ok(contents) => contents,
        Err(err) => {
            println!("cargo:warning=failed to read {var_name} from {path}: {err}");
            String::new()
        }
    }
}
