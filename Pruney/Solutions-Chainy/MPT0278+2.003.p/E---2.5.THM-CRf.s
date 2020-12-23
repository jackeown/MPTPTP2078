%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:07 EST 2020

% Result     : Theorem 0.33s
% Output     : CNFRefutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   30 (  37 expanded)
%              Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 102 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    inference(assume_negation,[status(cth)],[t79_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X19,X18)
        | r1_tarski(X19,X17)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r1_tarski(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r2_hidden(esk2_2(X21,X22),X22)
        | ~ r1_tarski(esk2_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) )
      & ( r2_hidden(esk2_2(X21,X22),X22)
        | r1_tarski(esk2_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_8,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | r1_tarski(k3_xboole_0(X12,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

fof(c_0_9,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),X1)
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k3_xboole_0(esk3_0,X1),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,esk1_2(k1_zfmisc_1(X1),X2)) = esk1_2(k1_zfmisc_1(X1),X2)
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_2(k1_zfmisc_1(esk3_0),X1),k1_zfmisc_1(esk4_0))
    | r1_tarski(k1_zfmisc_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.33/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.33/0.52  # and selection function SelectSmallestOrientable.
% 0.33/0.52  #
% 0.33/0.52  # Preprocessing time       : 0.026 s
% 0.33/0.52  # Presaturation interreduction done
% 0.33/0.52  
% 0.33/0.52  # Proof found!
% 0.33/0.52  # SZS status Theorem
% 0.33/0.52  # SZS output start CNFRefutation
% 0.33/0.52  fof(t79_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 0.33/0.52  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.33/0.52  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 0.33/0.52  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.33/0.52  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.33/0.52  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.33/0.52  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)))), inference(assume_negation,[status(cth)],[t79_zfmisc_1])).
% 0.33/0.52  fof(c_0_7, plain, ![X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X19,X18)|r1_tarski(X19,X17)|X18!=k1_zfmisc_1(X17))&(~r1_tarski(X20,X17)|r2_hidden(X20,X18)|X18!=k1_zfmisc_1(X17)))&((~r2_hidden(esk2_2(X21,X22),X22)|~r1_tarski(esk2_2(X21,X22),X21)|X22=k1_zfmisc_1(X21))&(r2_hidden(esk2_2(X21,X22),X22)|r1_tarski(esk2_2(X21,X22),X21)|X22=k1_zfmisc_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.33/0.52  fof(c_0_8, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|r1_tarski(k3_xboole_0(X12,X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 0.33/0.52  fof(c_0_9, negated_conjecture, (r1_tarski(esk3_0,esk4_0)&~r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.33/0.52  cnf(c_0_10, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.33/0.52  fof(c_0_11, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.33/0.52  cnf(c_0_12, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.33/0.52  cnf(c_0_13, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.33/0.52  cnf(c_0_14, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.33/0.52  fof(c_0_15, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.33/0.52  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_10])).
% 0.33/0.52  cnf(c_0_17, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.33/0.52  fof(c_0_18, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.33/0.52  cnf(c_0_19, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_12])).
% 0.33/0.52  cnf(c_0_20, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.33/0.52  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.33/0.52  cnf(c_0_22, plain, (r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),X1)|r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.33/0.52  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.33/0.52  cnf(c_0_24, negated_conjecture, (r2_hidden(k3_xboole_0(esk3_0,X1),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.33/0.52  cnf(c_0_25, plain, (k3_xboole_0(X1,esk1_2(k1_zfmisc_1(X1),X2))=esk1_2(k1_zfmisc_1(X1),X2)|r1_tarski(k1_zfmisc_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.33/0.52  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.33/0.52  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_2(k1_zfmisc_1(esk3_0),X1),k1_zfmisc_1(esk4_0))|r1_tarski(k1_zfmisc_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.33/0.52  cnf(c_0_28, negated_conjecture, (~r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.33/0.52  cnf(c_0_29, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), ['proof']).
% 0.33/0.52  # SZS output end CNFRefutation
% 0.33/0.52  # Proof object total steps             : 30
% 0.33/0.52  # Proof object clause steps            : 17
% 0.33/0.52  # Proof object formula steps           : 13
% 0.33/0.52  # Proof object conjectures             : 9
% 0.33/0.52  # Proof object clause conjectures      : 6
% 0.33/0.52  # Proof object formula conjectures     : 3
% 0.33/0.52  # Proof object initial clauses used    : 9
% 0.33/0.52  # Proof object initial formulas used   : 6
% 0.33/0.52  # Proof object generating inferences   : 6
% 0.33/0.52  # Proof object simplifying inferences  : 4
% 0.33/0.52  # Training examples: 0 positive, 0 negative
% 0.33/0.52  # Parsed axioms                        : 6
% 0.33/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.33/0.52  # Initial clauses                      : 12
% 0.33/0.52  # Removed in clause preprocessing      : 0
% 0.33/0.52  # Initial clauses in saturation        : 12
% 0.33/0.52  # Processed clauses                    : 970
% 0.33/0.52  # ...of these trivial                  : 98
% 0.33/0.52  # ...subsumed                          : 510
% 0.33/0.52  # ...remaining for further processing  : 362
% 0.33/0.52  # Other redundant clauses eliminated   : 2
% 0.33/0.52  # Clauses deleted for lack of memory   : 0
% 0.33/0.52  # Backward-subsumed                    : 0
% 0.33/0.52  # Backward-rewritten                   : 0
% 0.33/0.52  # Generated clauses                    : 8682
% 0.33/0.52  # ...of the previous two non-trivial   : 7797
% 0.33/0.52  # Contextual simplify-reflections      : 0
% 0.33/0.52  # Paramodulations                      : 8674
% 0.33/0.52  # Factorizations                       : 6
% 0.33/0.52  # Equation resolutions                 : 2
% 0.33/0.52  # Propositional unsat checks           : 0
% 0.33/0.52  #    Propositional check models        : 0
% 0.33/0.52  #    Propositional check unsatisfiable : 0
% 0.33/0.52  #    Propositional clauses             : 0
% 0.33/0.52  #    Propositional clauses after purity: 0
% 0.33/0.52  #    Propositional unsat core size     : 0
% 0.33/0.52  #    Propositional preprocessing time  : 0.000
% 0.33/0.52  #    Propositional encoding time       : 0.000
% 0.33/0.52  #    Propositional solver time         : 0.000
% 0.33/0.52  #    Success case prop preproc time    : 0.000
% 0.33/0.52  #    Success case prop encoding time   : 0.000
% 0.33/0.52  #    Success case prop solver time     : 0.000
% 0.33/0.52  # Current number of processed clauses  : 348
% 0.33/0.52  #    Positive orientable unit clauses  : 58
% 0.33/0.52  #    Positive unorientable unit clauses: 1
% 0.33/0.52  #    Negative unit clauses             : 1
% 0.33/0.52  #    Non-unit-clauses                  : 288
% 0.33/0.52  # Current number of unprocessed clauses: 6847
% 0.33/0.52  # ...number of literals in the above   : 35876
% 0.33/0.52  # Current number of archived formulas  : 0
% 0.33/0.52  # Current number of archived clauses   : 12
% 0.33/0.52  # Clause-clause subsumption calls (NU) : 13139
% 0.33/0.52  # Rec. Clause-clause subsumption calls : 7006
% 0.33/0.52  # Non-unit clause-clause subsumptions  : 510
% 0.33/0.52  # Unit Clause-clause subsumption calls : 168
% 0.33/0.52  # Rewrite failures with RHS unbound    : 0
% 0.33/0.52  # BW rewrite match attempts            : 292
% 0.33/0.52  # BW rewrite match successes           : 2
% 0.33/0.52  # Condensation attempts                : 0
% 0.33/0.52  # Condensation successes               : 0
% 0.33/0.52  # Termbank termtop insertions          : 189676
% 0.33/0.52  
% 0.33/0.52  # -------------------------------------------------
% 0.33/0.52  # User time                : 0.158 s
% 0.33/0.52  # System time              : 0.010 s
% 0.33/0.52  # Total time               : 0.168 s
% 0.33/0.52  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
