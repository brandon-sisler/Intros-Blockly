import {Proposition} from '../utils'

export default {
    "type": "theorem",
    "message0": "Theorem %1 %2",
    "args0": [
      {
        "type": "field_input",
        "name": "NAME",
        "text": "My Theorem",
      },
      {
        "type": "input_value",
        "name": "PROPOSITION",
        "check": Proposition,
      }
    ],
    "message1": "Proof %1",
    "args1": [
      {
        "type": "input_statement",
        "name": "ARGUMENT"
      }
    ],
    "message2": "Q.E.D. %1",
    "args2": [
      {
        "type": "input_dummy",
        "align": "RIGHT",
      }
    ],
    "colour": 230,
}