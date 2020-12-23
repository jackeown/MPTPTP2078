%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:46 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   24 (  37 expanded)
%              Number of clauses        :   13 (  16 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   88 ( 165 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r8_relat_2(X1,X2)
        <=> ! [X3,X4,X5] :
              ( ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & r2_hidden(X5,X2)
                & r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(k4_tarski(X4,X5),X1) )
             => r2_hidden(k4_tarski(X3,X5),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(l2_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> ! [X2,X3,X4] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X4),X1) )
           => r2_hidden(k4_tarski(X2,X4),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_wellord1)).

fof(t3_wellord2,axiom,(
    ! [X1] : v8_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_wellord2)).

fof(t30_wellord2,conjecture,(
    ! [X1] : r8_relat_2(k1_wellord2(X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord2)).

fof(c_0_5,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r8_relat_2(X13,X14)
        | ~ r2_hidden(X15,X14)
        | ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X17,X14)
        | ~ r2_hidden(k4_tarski(X15,X16),X13)
        | ~ r2_hidden(k4_tarski(X16,X17),X13)
        | r2_hidden(k4_tarski(X15,X17),X13)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk4_2(X13,X18),X18)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk5_2(X13,X18),X18)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk6_2(X13,X18),X18)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk4_2(X13,X18),esk5_2(X13,X18)),X13)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk5_2(X13,X18),esk6_2(X13,X18)),X13)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X13,X18),esk6_2(X13,X18)),X13)
        | r8_relat_2(X13,X18)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_2])])])])])])).

fof(c_0_6,plain,(
    ! [X22] : v1_relat_1(k1_wellord2(X22)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_7,plain,(
    ! [X6,X7,X8,X9] :
      ( ( ~ v8_relat_2(X6)
        | ~ r2_hidden(k4_tarski(X7,X8),X6)
        | ~ r2_hidden(k4_tarski(X8,X9),X6)
        | r2_hidden(k4_tarski(X7,X9),X6)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk1_1(X6),esk2_1(X6)),X6)
        | v8_relat_2(X6)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk2_1(X6),esk3_1(X6)),X6)
        | v8_relat_2(X6)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_1(X6),esk3_1(X6)),X6)
        | v8_relat_2(X6)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)
    | r8_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X23] : v8_relat_2(k1_wellord2(X23)) ),
    inference(variable_rename,[status(thm)],[t3_wellord2])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(X2,X4),X1)
    | ~ v8_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r8_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(k4_tarski(esk5_2(k1_wellord2(X1),X2),esk6_2(k1_wellord2(X1),X2)),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( v8_relat_2(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | r8_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] : r8_relat_2(k1_wellord2(X1),X1) ),
    inference(assume_negation,[status(cth)],[t30_wellord2])).

cnf(c_0_16,plain,
    ( r8_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(k4_tarski(X3,esk6_2(k1_wellord2(X1),X2)),k1_wellord2(X1))
    | ~ r2_hidden(k4_tarski(X3,esk5_2(k1_wellord2(X1),X2)),k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_9])])).

cnf(c_0_17,plain,
    ( r8_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(k4_tarski(esk4_2(k1_wellord2(X1),X2),esk5_2(k1_wellord2(X1),X2)),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_9])).

fof(c_0_18,negated_conjecture,(
    ~ r8_relat_2(k1_wellord2(esk7_0),esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_19,plain,
    ( r8_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),esk6_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,plain,
    ( r8_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(k4_tarski(esk4_2(k1_wellord2(X1),X2),esk6_2(k1_wellord2(X1),X2)),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( ~ r8_relat_2(k1_wellord2(esk7_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r8_relat_2(k1_wellord2(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_9])])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:53:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.027 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(d8_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r8_relat_2(X1,X2)<=>![X3, X4, X5]:(((((r2_hidden(X3,X2)&r2_hidden(X4,X2))&r2_hidden(X5,X2))&r2_hidden(k4_tarski(X3,X4),X1))&r2_hidden(k4_tarski(X4,X5),X1))=>r2_hidden(k4_tarski(X3,X5),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_2)).
% 0.14/0.39  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.14/0.39  fof(l2_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v8_relat_2(X1)<=>![X2, X3, X4]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X3,X4),X1))=>r2_hidden(k4_tarski(X2,X4),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l2_wellord1)).
% 0.14/0.39  fof(t3_wellord2, axiom, ![X1]:v8_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_wellord2)).
% 0.14/0.39  fof(t30_wellord2, conjecture, ![X1]:r8_relat_2(k1_wellord2(X1),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_wellord2)).
% 0.14/0.39  fof(c_0_5, plain, ![X13, X14, X15, X16, X17, X18]:((~r8_relat_2(X13,X14)|(~r2_hidden(X15,X14)|~r2_hidden(X16,X14)|~r2_hidden(X17,X14)|~r2_hidden(k4_tarski(X15,X16),X13)|~r2_hidden(k4_tarski(X16,X17),X13)|r2_hidden(k4_tarski(X15,X17),X13))|~v1_relat_1(X13))&((((((r2_hidden(esk4_2(X13,X18),X18)|r8_relat_2(X13,X18)|~v1_relat_1(X13))&(r2_hidden(esk5_2(X13,X18),X18)|r8_relat_2(X13,X18)|~v1_relat_1(X13)))&(r2_hidden(esk6_2(X13,X18),X18)|r8_relat_2(X13,X18)|~v1_relat_1(X13)))&(r2_hidden(k4_tarski(esk4_2(X13,X18),esk5_2(X13,X18)),X13)|r8_relat_2(X13,X18)|~v1_relat_1(X13)))&(r2_hidden(k4_tarski(esk5_2(X13,X18),esk6_2(X13,X18)),X13)|r8_relat_2(X13,X18)|~v1_relat_1(X13)))&(~r2_hidden(k4_tarski(esk4_2(X13,X18),esk6_2(X13,X18)),X13)|r8_relat_2(X13,X18)|~v1_relat_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_2])])])])])])).
% 0.14/0.39  fof(c_0_6, plain, ![X22]:v1_relat_1(k1_wellord2(X22)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.14/0.39  fof(c_0_7, plain, ![X6, X7, X8, X9]:((~v8_relat_2(X6)|(~r2_hidden(k4_tarski(X7,X8),X6)|~r2_hidden(k4_tarski(X8,X9),X6)|r2_hidden(k4_tarski(X7,X9),X6))|~v1_relat_1(X6))&(((r2_hidden(k4_tarski(esk1_1(X6),esk2_1(X6)),X6)|v8_relat_2(X6)|~v1_relat_1(X6))&(r2_hidden(k4_tarski(esk2_1(X6),esk3_1(X6)),X6)|v8_relat_2(X6)|~v1_relat_1(X6)))&(~r2_hidden(k4_tarski(esk1_1(X6),esk3_1(X6)),X6)|v8_relat_2(X6)|~v1_relat_1(X6)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).
% 0.14/0.39  cnf(c_0_8, plain, (r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)|r8_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.39  cnf(c_0_9, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.39  fof(c_0_10, plain, ![X23]:v8_relat_2(k1_wellord2(X23)), inference(variable_rename,[status(thm)],[t3_wellord2])).
% 0.14/0.39  cnf(c_0_11, plain, (r2_hidden(k4_tarski(X2,X4),X1)|~v8_relat_2(X1)|~r2_hidden(k4_tarski(X2,X3),X1)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  cnf(c_0_12, plain, (r8_relat_2(k1_wellord2(X1),X2)|r2_hidden(k4_tarski(esk5_2(k1_wellord2(X1),X2),esk6_2(k1_wellord2(X1),X2)),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.14/0.39  cnf(c_0_13, plain, (v8_relat_2(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_14, plain, (r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)|r8_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.39  fof(c_0_15, negated_conjecture, ~(![X1]:r8_relat_2(k1_wellord2(X1),X1)), inference(assume_negation,[status(cth)],[t30_wellord2])).
% 0.14/0.39  cnf(c_0_16, plain, (r8_relat_2(k1_wellord2(X1),X2)|r2_hidden(k4_tarski(X3,esk6_2(k1_wellord2(X1),X2)),k1_wellord2(X1))|~r2_hidden(k4_tarski(X3,esk5_2(k1_wellord2(X1),X2)),k1_wellord2(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_9])])).
% 0.14/0.39  cnf(c_0_17, plain, (r8_relat_2(k1_wellord2(X1),X2)|r2_hidden(k4_tarski(esk4_2(k1_wellord2(X1),X2),esk5_2(k1_wellord2(X1),X2)),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_14, c_0_9])).
% 0.14/0.39  fof(c_0_18, negated_conjecture, ~r8_relat_2(k1_wellord2(esk7_0),esk7_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.14/0.39  cnf(c_0_19, plain, (r8_relat_2(X1,X2)|~r2_hidden(k4_tarski(esk4_2(X1,X2),esk6_2(X1,X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.39  cnf(c_0_20, plain, (r8_relat_2(k1_wellord2(X1),X2)|r2_hidden(k4_tarski(esk4_2(k1_wellord2(X1),X2),esk6_2(k1_wellord2(X1),X2)),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.39  cnf(c_0_21, negated_conjecture, (~r8_relat_2(k1_wellord2(esk7_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_22, plain, (r8_relat_2(k1_wellord2(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_9])])).
% 0.14/0.39  cnf(c_0_23, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 24
% 0.14/0.39  # Proof object clause steps            : 13
% 0.14/0.39  # Proof object formula steps           : 11
% 0.14/0.39  # Proof object conjectures             : 5
% 0.14/0.39  # Proof object clause conjectures      : 2
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 7
% 0.14/0.39  # Proof object initial formulas used   : 5
% 0.14/0.39  # Proof object generating inferences   : 5
% 0.14/0.39  # Proof object simplifying inferences  : 7
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 5
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 14
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 14
% 0.14/0.39  # Processed clauses                    : 37
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 0
% 0.14/0.39  # ...remaining for further processing  : 37
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 9
% 0.14/0.39  # Generated clauses                    : 15
% 0.14/0.39  # ...of the previous two non-trivial   : 13
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 15
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 0
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 14
% 0.14/0.39  #    Positive orientable unit clauses  : 3
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 0
% 0.14/0.39  #    Non-unit-clauses                  : 11
% 0.14/0.39  # Current number of unprocessed clauses: 4
% 0.14/0.39  # ...number of literals in the above   : 24
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 23
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 67
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 31
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.39  # Unit Clause-clause subsumption calls : 0
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 2
% 0.14/0.39  # BW rewrite match successes           : 2
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 1742
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.027 s
% 0.14/0.39  # System time              : 0.005 s
% 0.14/0.39  # Total time               : 0.032 s
% 0.14/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
