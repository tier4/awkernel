# Crop box filter

This `no_std` library uses `alloc` and filters the point clouds defined by
[common types](../common_types/README.md). It is not yet connected to the
Autoware application pipeline (`run()` is currently empty).

## Types

| Type | Purpose |
| --- | --- |
| `CropBoxParam` | Minimum and maximum limits for x, y, and z. Its `polygon` method builds the box outline. |
| `CropBoxFilterConfig` | Box limits, inside/outside selection, and optional preprocessing and postprocessing transforms. |
| `CropBoxFilter` | Precomputes transform matrices and filters a borrowed `PointCloud`. |
| `CropBoxFilterResult` | The output cloud and `skipped_nan_count`. Despite its name, the count includes all points with non-finite original coordinates, including infinities. |
| `CropBoxFilterError` | Reports field, cloud, point-bound, and overflow failures. |

`generate_crop_box_polygon` returns the box outline as a `PolygonStamped` with
the caller-supplied frame and timestamp.

## Usage

```rust
use common_types::point::PointCloud;
use crop_box_filter::{CropBoxFilter, CropBoxFilterConfig, CropBoxFilterError, CropBoxFilterResult, CropBoxParam};

fn crop(cloud: &PointCloud) -> Result<CropBoxFilterResult, CropBoxFilterError> {
    let filter = CropBoxFilter::new(CropBoxFilterConfig {
        param: CropBoxParam {
            min_x: -1.0, max_x: 1.0,
            min_y: -1.0, max_y: 1.0,
            min_z: -1.0, max_z: 1.0,
        },
        keep_outside_box: false,
        preprocess_transform: None,
        postprocess_transform: None,
    });
    filter.filter(cloud)
}
```

## Filtering behavior

The filter:

1. Validates native byte order and selects `x`, `y`, and `z` as nonempty
   `Float32` fields, including for empty clouds. It uses the first value of
   each coordinate field.
2. Skips points whose original x, y, or z is NaN or infinite.
3. Applies the optional preprocessing transform, then tests the transformed
   coordinates against strict bounds (`min < coordinate < max`). Faces,
   edges, and corners are outside. `keep_outside_box` inverts this selection.
4. Copies each retained point's complete bytes in input order, applies the
   optional postprocessing transform, and writes the transformed x/y/z first
   values into the output. Other bytes and point padding are retained, except
   where their fields overlap the coordinate writes; input row padding is not
   copied.

The output is an unorganized cloud (`height = 1`) with packed rows, original
field descriptors, point stride, byte-order flag, density flag, and timestamp.
Its frame ID is the postprocessing transform's header frame if present,
otherwise the preprocessing transform's header frame if present, otherwise
the input frame. Transform frame IDs are not validated against the input or
each other: callers must supply transforms compatible with their coordinate
frames. In particular, the bounds apply in the preprocessing output frame, or
the input frame when no preprocessing transform is supplied.

The filter receives transforms directly; it does not consult a transform
listener. It allocates an output byte buffer with the input data length as its
initial capacity and a transformed-coordinate buffer with the input point
count as its initial capacity. No execution-time or memory benchmarks, or
pinned differential comparison against an Autoware reference, are provided
here.

## Validation

From the repository root:

```sh
cargo build -p crop_box_filter --all-targets --all-features
cargo test -p crop_box_filter --all-features
```

Tests cover empty clouds, strict boundaries, invalid coordinates, transforms,
metadata, extra values, unaligned fields, and padded input rows.
