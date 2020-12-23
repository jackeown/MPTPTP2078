%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:22 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   25 (  46 expanded)
%              Number of clauses        :   16 (  22 expanded)
%              Number of leaves         :    4 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 147 expanded)
%              Number of equality atoms :   12 (  30 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t76_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_5,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k4_xboole_0(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_xboole_0(X1,X2)
       => r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2)) ) ),
    inference(assume_negation,[status(cth)],[t76_xboole_1])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_10,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0)
    & ~ r1_xboole_0(k3_xboole_0(esk5_0,esk3_0),k3_xboole_0(esk5_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X4,k4_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | r2_hidden(esk2_2(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_xboole_0(k3_xboole_0(esk5_0,esk3_0),k3_xboole_0(esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,esk4_0)))
    | ~ r2_hidden(esk2_2(X1,k4_xboole_0(X2,k4_xboole_0(X2,esk4_0))),esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | r2_hidden(esk2_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_8]),c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)),k4_xboole_0(X2,k4_xboole_0(X2,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:20:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.78/1.00  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.78/1.00  # and selection function SelectNewComplexAHP.
% 0.78/1.00  #
% 0.78/1.00  # Preprocessing time       : 0.027 s
% 0.78/1.00  
% 0.78/1.00  # Proof found!
% 0.78/1.00  # SZS status Theorem
% 0.78/1.00  # SZS output start CNFRefutation
% 0.78/1.00  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.78/1.00  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.78/1.00  fof(t76_xboole_1, conjecture, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 0.78/1.00  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.78/1.00  fof(c_0_4, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.78/1.00  fof(c_0_5, plain, ![X20, X21]:k4_xboole_0(X20,k4_xboole_0(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.78/1.00  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2)))), inference(assume_negation,[status(cth)],[t76_xboole_1])).
% 0.78/1.00  cnf(c_0_7, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.78/1.00  cnf(c_0_8, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.78/1.00  fof(c_0_9, plain, ![X14, X15, X17, X18, X19]:(((r2_hidden(esk2_2(X14,X15),X14)|r1_xboole_0(X14,X15))&(r2_hidden(esk2_2(X14,X15),X15)|r1_xboole_0(X14,X15)))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|~r1_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.78/1.00  fof(c_0_10, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)&~r1_xboole_0(k3_xboole_0(esk5_0,esk3_0),k3_xboole_0(esk5_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.78/1.00  cnf(c_0_11, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X4,k4_xboole_0(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_7, c_0_8])).
% 0.78/1.00  cnf(c_0_12, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.78/1.00  cnf(c_0_13, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.78/1.00  cnf(c_0_14, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(er,[status(thm)],[c_0_11])).
% 0.78/1.00  cnf(c_0_15, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.78/1.00  cnf(c_0_16, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.78/1.00  cnf(c_0_17, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|r2_hidden(esk2_2(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),X3)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.78/1.00  cnf(c_0_18, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.78/1.00  cnf(c_0_19, negated_conjecture, (~r1_xboole_0(k3_xboole_0(esk5_0,esk3_0),k3_xboole_0(esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.78/1.00  cnf(c_0_20, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,esk4_0)))|~r2_hidden(esk2_2(X1,k4_xboole_0(X2,k4_xboole_0(X2,esk4_0))),esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.78/1.00  cnf(c_0_21, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|r2_hidden(esk2_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X2)), inference(spm,[status(thm)],[c_0_14, c_0_18])).
% 0.78/1.00  cnf(c_0_22, negated_conjecture, (~r1_xboole_0(k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_8]), c_0_8])).
% 0.78/1.00  cnf(c_0_23, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,esk3_0)),k4_xboole_0(X2,k4_xboole_0(X2,esk4_0)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.78/1.00  cnf(c_0_24, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23])]), ['proof']).
% 0.78/1.00  # SZS output end CNFRefutation
% 0.78/1.00  # Proof object total steps             : 25
% 0.78/1.00  # Proof object clause steps            : 16
% 0.78/1.00  # Proof object formula steps           : 9
% 0.78/1.00  # Proof object conjectures             : 10
% 0.78/1.00  # Proof object clause conjectures      : 7
% 0.78/1.00  # Proof object formula conjectures     : 3
% 0.78/1.00  # Proof object initial clauses used    : 7
% 0.78/1.00  # Proof object initial formulas used   : 4
% 0.78/1.00  # Proof object generating inferences   : 6
% 0.78/1.00  # Proof object simplifying inferences  : 5
% 0.78/1.00  # Training examples: 0 positive, 0 negative
% 0.78/1.00  # Parsed axioms                        : 4
% 0.78/1.00  # Removed by relevancy pruning/SinE    : 0
% 0.78/1.00  # Initial clauses                      : 12
% 0.78/1.00  # Removed in clause preprocessing      : 1
% 0.78/1.00  # Initial clauses in saturation        : 11
% 0.78/1.00  # Processed clauses                    : 1179
% 0.78/1.00  # ...of these trivial                  : 35
% 0.78/1.00  # ...subsumed                          : 471
% 0.78/1.00  # ...remaining for further processing  : 673
% 0.78/1.00  # Other redundant clauses eliminated   : 254
% 0.78/1.00  # Clauses deleted for lack of memory   : 0
% 0.78/1.00  # Backward-subsumed                    : 21
% 0.78/1.00  # Backward-rewritten                   : 48
% 0.78/1.00  # Generated clauses                    : 23556
% 0.78/1.00  # ...of the previous two non-trivial   : 20990
% 0.78/1.00  # Contextual simplify-reflections      : 3
% 0.78/1.00  # Paramodulations                      : 22729
% 0.78/1.00  # Factorizations                       : 88
% 0.78/1.00  # Equation resolutions                 : 271
% 0.78/1.00  # Propositional unsat checks           : 0
% 0.78/1.00  #    Propositional check models        : 0
% 0.78/1.00  #    Propositional check unsatisfiable : 0
% 0.78/1.00  #    Propositional clauses             : 0
% 0.78/1.00  #    Propositional clauses after purity: 0
% 0.78/1.00  #    Propositional unsat core size     : 0
% 0.78/1.00  #    Propositional preprocessing time  : 0.000
% 0.78/1.00  #    Propositional encoding time       : 0.000
% 0.78/1.00  #    Propositional solver time         : 0.000
% 0.78/1.00  #    Success case prop preproc time    : 0.000
% 0.78/1.00  #    Success case prop encoding time   : 0.000
% 0.78/1.00  #    Success case prop solver time     : 0.000
% 0.78/1.00  # Current number of processed clauses  : 604
% 0.78/1.00  #    Positive orientable unit clauses  : 55
% 0.78/1.00  #    Positive unorientable unit clauses: 0
% 0.78/1.00  #    Negative unit clauses             : 148
% 0.78/1.00  #    Non-unit-clauses                  : 401
% 0.78/1.00  # Current number of unprocessed clauses: 19708
% 0.78/1.00  # ...number of literals in the above   : 103207
% 0.78/1.00  # Current number of archived formulas  : 0
% 0.78/1.00  # Current number of archived clauses   : 70
% 0.78/1.00  # Clause-clause subsumption calls (NU) : 15758
% 0.78/1.00  # Rec. Clause-clause subsumption calls : 12189
% 0.78/1.00  # Non-unit clause-clause subsumptions  : 417
% 0.78/1.00  # Unit Clause-clause subsumption calls : 11629
% 0.78/1.00  # Rewrite failures with RHS unbound    : 0
% 0.78/1.00  # BW rewrite match attempts            : 72
% 0.78/1.00  # BW rewrite match successes           : 18
% 0.78/1.00  # Condensation attempts                : 0
% 0.78/1.00  # Condensation successes               : 0
% 0.78/1.00  # Termbank termtop insertions          : 466208
% 0.78/1.00  
% 0.78/1.00  # -------------------------------------------------
% 0.78/1.00  # User time                : 0.656 s
% 0.78/1.00  # System time              : 0.017 s
% 0.78/1.00  # Total time               : 0.673 s
% 0.78/1.00  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
