from oso import Oso


def setup_oso():
    oso = Oso()
    return oso


oso = setup_oso()

actor = "alice@example.com"
resource = EXPENSES[1]
oso.allow(actor, "GET", resource)
