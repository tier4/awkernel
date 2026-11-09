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
use common_types::point_cloud::PointCloud;
use crop_box_filter::{CropBoxFilter, CropBoxFilterConfig, CropBoxFilterError, CropBoxFilterResult, CropBoxParam};

fn crop(cloud: &PointCloud) -> Result<CropBoxFilterResult, CropBoxFilterError> {
    let filter = CropBoxFilter::new(CropBoxFilterConfig {
        param: CropBoxParam::try_new(-1.0, 1.0, -1.0, 1.0, -1.0, 1.0)?,
        keep_outside_box: false,
        preprocess_transform: None,
        postprocess_transform: None,
    });
    filter.filter(cloud)
}
```

## Filtering behavior

The filter:

1. Accepts a `PointCloud` constructed with `PointCloud::try_new`, which checks
   native byte order and the entire layout, including unused fields. It selects
   the first field matching both name and `Float32` type for each of `x`, `y`,
   and `z`; earlier same-name fields of other types are skipped. The selected
   fields' first values are used. Zero-count coordinates fail with
   `ValueOutOfBounds` when a point is read; empty clouds accept them because
   no coordinate values are accessed.
2. Skips points whose original x, y, or z is NaN or infinite.
3. Applies the optional preprocessing transform, then tests the transformed
   coordinates against strict bounds (`min < coordinate < max`). Faces,
   edges, and corners are outside. `keep_outside_box` inverts this selection.
4. Copies each retained point's complete bytes in input order, applies the
   optional postprocessing transform, and writes the transformed x/y/z first
   values into the output. Other bytes and point padding are retained, except
   where their fields overlap the coordinate writes; writes occur in x, y, z
   order. Input row padding and trailing bytes are not copied.

For nonempty output, the cloud is packed (`height = 1`, `width = retained
count`, `row_step = data.len()`). Empty output has `height = 0`, `width = 1`,
`row_step = point_step`, and no data: `PointCloud` does not permit zero width.
Use `point_count()` or `height()` rather than `width()` alone to detect an
empty output. Both forms retain the original field descriptors, point stride,
byte-order flag, density flag, and timestamp.
Its frame ID is the postprocessing transform's header frame if present,
otherwise the preprocessing transform's header frame if present, otherwise
the input frame. Transform frame IDs are not validated against the input or
each other: callers must supply transforms compatible with their coordinate
frames. In particular, the bounds apply in the preprocessing output frame, or
the input frame when no preprocessing transform is supplied.

The filter receives transforms directly; it does not consult a transform
listener. The migration replaces the removed tuple reader with reusable typed
field descriptors; it still copies and updates each retained point in one
pass, without a separate transformed-coordinate buffer. It allocates an output
byte buffer with the input data length as its initial capacity and clones the
field descriptors. For F fields, N points, point stride S, and K retained points,
the work is O(F + N + K·S); output capacity is O(D + F), where D is input data
length including row padding and trailing bytes. Allocator behavior and input
sizes are not bounded here, so this is not an allocation-free hard-real-time
path. No execution-time or memory benchmarks, or pinned differential comparison
against an Autoware reference, are provided here.

## Validation

From the repository root:

```sh
cargo build -p crop_box_filter --all-targets --all-features
cargo clippy -p crop_box_filter --all-targets --all-features -- -D warnings
cargo test -p crop_box_filter --all-features
```

Tests cover empty clouds, strict boundaries, invalid coordinates, transforms,
metadata, extra values, unaligned fields, and padded input rows.
