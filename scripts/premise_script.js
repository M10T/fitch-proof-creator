function add_premise() {
    const button = $("label#lResult").first();
    const newInput = $("<input type='text' name='premise'/>");
    const newLabel = $("<label>Premise: </label>");

    button.before(newLabel);
    button.before(newInput);
    button.before($("<br/>"));
}

function remove_premise() {
    if ($('input:not(#result)').size() == 0) return;
    $("input:not(#result)").last().remove();
    $("label:not(#lResult)").last().remove();
    $("br:not(.submit)").last().remove();
}