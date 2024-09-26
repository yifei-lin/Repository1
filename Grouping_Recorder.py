

class GroupingRecorder:
    def __init__(self):
        self.grouping_operations = []

    def record(self, node1_id, node2_id, new_group_id):
        self.grouping_operations.append((node1_id, node2_id, new_group_id))