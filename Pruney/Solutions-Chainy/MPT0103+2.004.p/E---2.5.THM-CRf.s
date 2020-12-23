%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:06 EST 2020

% Result     : Theorem 21.80s
% Output     : CNFRefutation 21.80s
% Verified   : 
% Statistics : Number of formulae       :   23 (  30 expanded)
%              Number of clauses        :   14 (  15 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 127 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t96_xboole_1,conjecture,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

fof(c_0_4,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_5,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_7,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r2_hidden(X20,X21)
        | ~ r2_hidden(X20,X22)
        | ~ r2_hidden(X20,k5_xboole_0(X21,X22)) )
      & ( r2_hidden(X20,X21)
        | r2_hidden(X20,X22)
        | ~ r2_hidden(X20,k5_xboole_0(X21,X22)) )
      & ( ~ r2_hidden(X20,X21)
        | r2_hidden(X20,X22)
        | r2_hidden(X20,k5_xboole_0(X21,X22)) )
      & ( ~ r2_hidden(X20,X22)
        | r2_hidden(X20,X21)
        | r2_hidden(X20,k5_xboole_0(X21,X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t96_xboole_1])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),k5_xboole_0(X1,X4))
    | r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X4)
    | r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_17,negated_conjecture,(
    ~ r1_tarski(k4_xboole_0(esk3_0,esk4_0),k5_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_18,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),k5_xboole_0(X1,X3)),X3)
    | r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk3_0,esk4_0),k5_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 21.80/22.00  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 21.80/22.00  # and selection function SelectNewComplexAHP.
% 21.80/22.00  #
% 21.80/22.00  # Preprocessing time       : 0.027 s
% 21.80/22.00  
% 21.80/22.00  # Proof found!
% 21.80/22.00  # SZS status Theorem
% 21.80/22.00  # SZS output start CNFRefutation
% 21.80/22.00  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 21.80/22.00  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 21.80/22.00  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 21.80/22.00  fof(t96_xboole_1, conjecture, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 21.80/22.00  fof(c_0_4, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 21.80/22.00  cnf(c_0_5, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 21.80/22.00  fof(c_0_6, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 21.80/22.00  fof(c_0_7, plain, ![X20, X21, X22]:(((~r2_hidden(X20,X21)|~r2_hidden(X20,X22)|~r2_hidden(X20,k5_xboole_0(X21,X22)))&(r2_hidden(X20,X21)|r2_hidden(X20,X22)|~r2_hidden(X20,k5_xboole_0(X21,X22))))&((~r2_hidden(X20,X21)|r2_hidden(X20,X22)|r2_hidden(X20,k5_xboole_0(X21,X22)))&(~r2_hidden(X20,X22)|r2_hidden(X20,X21)|r2_hidden(X20,k5_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 21.80/22.00  cnf(c_0_8, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_5])).
% 21.80/22.00  cnf(c_0_9, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 21.80/22.00  cnf(c_0_10, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 21.80/22.00  cnf(c_0_11, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 21.80/22.00  cnf(c_0_12, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)|r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 21.80/22.00  fof(c_0_13, negated_conjecture, ~(![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t96_xboole_1])).
% 21.80/22.00  cnf(c_0_14, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_10])).
% 21.80/22.00  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 21.80/22.00  cnf(c_0_16, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),k5_xboole_0(X1,X4))|r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X4)|r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 21.80/22.00  fof(c_0_17, negated_conjecture, ~r1_tarski(k4_xboole_0(esk3_0,esk4_0),k5_xboole_0(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 21.80/22.00  cnf(c_0_18, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_14, c_0_9])).
% 21.80/22.00  cnf(c_0_19, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),k5_xboole_0(X1,X3)),X3)|r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 21.80/22.00  cnf(c_0_20, negated_conjecture, (~r1_tarski(k4_xboole_0(esk3_0,esk4_0),k5_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 21.80/22.00  cnf(c_0_21, plain, (r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 21.80/22.00  cnf(c_0_22, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21])]), ['proof']).
% 21.80/22.00  # SZS output end CNFRefutation
% 21.80/22.00  # Proof object total steps             : 23
% 21.80/22.00  # Proof object clause steps            : 14
% 21.80/22.00  # Proof object formula steps           : 9
% 21.80/22.00  # Proof object conjectures             : 5
% 21.80/22.00  # Proof object clause conjectures      : 2
% 21.80/22.00  # Proof object formula conjectures     : 3
% 21.80/22.00  # Proof object initial clauses used    : 6
% 21.80/22.00  # Proof object initial formulas used   : 4
% 21.80/22.00  # Proof object generating inferences   : 7
% 21.80/22.00  # Proof object simplifying inferences  : 2
% 21.80/22.00  # Training examples: 0 positive, 0 negative
% 21.80/22.00  # Parsed axioms                        : 4
% 21.80/22.00  # Removed by relevancy pruning/SinE    : 0
% 21.80/22.00  # Initial clauses                      : 14
% 21.80/22.00  # Removed in clause preprocessing      : 0
% 21.80/22.00  # Initial clauses in saturation        : 14
% 21.80/22.00  # Processed clauses                    : 92633
% 21.80/22.00  # ...of these trivial                  : 2644
% 21.80/22.00  # ...subsumed                          : 86059
% 21.80/22.00  # ...remaining for further processing  : 3930
% 21.80/22.00  # Other redundant clauses eliminated   : 7418
% 21.80/22.00  # Clauses deleted for lack of memory   : 96685
% 21.80/22.00  # Backward-subsumed                    : 68
% 21.80/22.00  # Backward-rewritten                   : 110
% 21.80/22.00  # Generated clauses                    : 2920007
% 21.80/22.00  # ...of the previous two non-trivial   : 2602021
% 21.80/22.00  # Contextual simplify-reflections      : 30
% 21.80/22.00  # Paramodulations                      : 2910904
% 21.80/22.00  # Factorizations                       : 1356
% 21.80/22.00  # Equation resolutions                 : 7747
% 21.80/22.00  # Propositional unsat checks           : 0
% 21.80/22.00  #    Propositional check models        : 0
% 21.80/22.00  #    Propositional check unsatisfiable : 0
% 21.80/22.00  #    Propositional clauses             : 0
% 21.80/22.00  #    Propositional clauses after purity: 0
% 21.80/22.00  #    Propositional unsat core size     : 0
% 21.80/22.00  #    Propositional preprocessing time  : 0.000
% 21.80/22.00  #    Propositional encoding time       : 0.000
% 21.80/22.00  #    Propositional solver time         : 0.000
% 21.80/22.00  #    Success case prop preproc time    : 0.000
% 21.80/22.00  #    Success case prop encoding time   : 0.000
% 21.80/22.00  #    Success case prop solver time     : 0.000
% 21.80/22.00  # Current number of processed clauses  : 3752
% 21.80/22.00  #    Positive orientable unit clauses  : 573
% 21.80/22.00  #    Positive unorientable unit clauses: 7
% 21.80/22.00  #    Negative unit clauses             : 37
% 21.80/22.00  #    Non-unit-clauses                  : 3135
% 21.80/22.00  # Current number of unprocessed clauses: 1332625
% 21.80/22.00  # ...number of literals in the above   : 3241656
% 21.80/22.00  # Current number of archived formulas  : 0
% 21.80/22.00  # Current number of archived clauses   : 178
% 21.80/22.00  # Clause-clause subsumption calls (NU) : 2154902
% 21.80/22.00  # Rec. Clause-clause subsumption calls : 1640043
% 21.80/22.00  # Non-unit clause-clause subsumptions  : 64431
% 21.80/22.00  # Unit Clause-clause subsumption calls : 80906
% 21.80/22.00  # Rewrite failures with RHS unbound    : 1406
% 21.80/22.00  # BW rewrite match attempts            : 17598
% 21.80/22.00  # BW rewrite match successes           : 126
% 21.80/22.00  # Condensation attempts                : 0
% 21.80/22.00  # Condensation successes               : 0
% 21.80/22.00  # Termbank termtop insertions          : 53157822
% 21.90/22.08  
% 21.90/22.08  # -------------------------------------------------
% 21.90/22.08  # User time                : 20.848 s
% 21.90/22.08  # System time              : 0.885 s
% 21.90/22.08  # Total time               : 21.733 s
% 21.90/22.08  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
