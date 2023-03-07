import {Proposition} from '../utils'

export default {
    "type": "combination",
    "message0": "%1 %2 %3",
    "args0": [
      {
        "type": "input_value",
        "name": "PROPOSITION1",
        "check": Proposition,
      },
      {
        "type": "field_dropdown",
        "name": "TYPE",
        "options": [
          [
            "∧",
            "and"
          ],
          [
            "∨",
            "or"
          ],
          [
            "→",
            "implies"
          ],
          [
            "↔",
            "iff"
          ],
        ]
      },
      {
        "type": "input_value",
        "name": "PROPOSITION2",
        "check": Proposition,
      },
    ],
    "inputsInline": true,
    "output": "Formula",
    "colour": 65,
    // "extensions": ["combinationMixin"]
  }