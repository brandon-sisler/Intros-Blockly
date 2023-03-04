<script lang="ts">
    import Blockly from 'blockly';
    import BlocklyComponent from '../lib/Blockly.svelte';
    import { toolbox } from '../lib/toolbox'
    let workspace : Blockly.WorkspaceSvg;
</script>

<BlocklyComponent {toolbox} bind:workspace={workspace}/>

<textarea id="blocklyProof" style="height: 320px; width: 500px;" readonly></textarea>
<textarea id="blocklyCoq" style="height: 320px; width: 500px;" readonly></textarea>