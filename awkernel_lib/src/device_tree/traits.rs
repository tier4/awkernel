use crate::device_tree::node::DeviceTreeNode;

pub trait HasNamedChildNode {
    /// Having child nodes or not
    fn has_children(&self) -> bool;

    /// Look for a child by its name
    fn find_child(&self, name: &str) -> Option<&DeviceTreeNode>;
}
