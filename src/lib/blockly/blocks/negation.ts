import {Proposition} from '../utils'

export default {
    "type": "negation",
    "message0": "¬ %1",
    "args0": [
      {
        "type": "input_value",
        "name": "PROPOSITION",
        "check": Proposition,
      },
    ],
    "inputsInline": true,
    "output": "Formula",
    "colour": 0,
    "helpUrl": ""
}