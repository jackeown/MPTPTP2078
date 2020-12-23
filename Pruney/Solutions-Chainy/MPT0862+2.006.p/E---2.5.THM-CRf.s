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
% DateTime   : Thu Dec  3 10:59:14 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   27 (  65 expanded)
%              Number of clauses        :   16 (  30 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 175 expanded)
%              Number of equality atoms :   43 ( 111 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),k2_tarski(X3,X4)))
     => ( k1_mcart_1(X1) = X2
        & ( k2_mcart_1(X1) = X3
          | k2_mcart_1(X1) = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t16_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,k2_tarski(X3,X4)))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & ( k2_mcart_1(X1) = X3
          | k2_mcart_1(X1) = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),k2_tarski(X3,X4)))
       => ( k1_mcart_1(X1) = X2
          & ( k2_mcart_1(X1) = X3
            | k2_mcart_1(X1) = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_mcart_1])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_7,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_8,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)))
    & ( k2_mcart_1(esk2_0) != esk4_0
      | k1_mcart_1(esk2_0) != esk3_0 )
    & ( k2_mcart_1(esk2_0) != esk5_0
      | k1_mcart_1(esk2_0) != esk3_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_9,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X13,X14,X15] :
      ( ( r2_hidden(k1_mcart_1(X13),X14)
        | ~ r2_hidden(X13,k2_zfmisc_1(X14,X15)) )
      & ( r2_hidden(k2_mcart_1(X13),X15)
        | ~ r2_hidden(X13,k2_zfmisc_1(X14,X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk3_0),k2_tarski(esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_10])).

fof(c_0_16,plain,(
    ! [X16,X17,X18,X19] :
      ( ( r2_hidden(k1_mcart_1(X16),X17)
        | ~ r2_hidden(X16,k2_zfmisc_1(X17,k2_tarski(X18,X19))) )
      & ( k2_mcart_1(X16) = X18
        | k2_mcart_1(X16) = X19
        | ~ r2_hidden(X16,k2_zfmisc_1(X17,k2_tarski(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_mcart_1])])])).

cnf(c_0_17,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),k2_tarski(esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( k2_mcart_1(X1) = X2
    | k2_mcart_1(X1) = X3
    | ~ r2_hidden(X1,k2_zfmisc_1(X4,k2_tarski(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk5_0
    | k1_mcart_1(esk2_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk4_0
    | k1_mcart_1(esk2_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk5_0
    | k2_mcart_1(esk2_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])])).

cnf(c_0_25,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_21])])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_23,c_0_24]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t18_mcart_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),k2_tarski(X3,X4)))=>(k1_mcart_1(X1)=X2&(k2_mcart_1(X1)=X3|k2_mcart_1(X1)=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_mcart_1)).
% 0.13/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.13/0.38  fof(t16_mcart_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(X2,k2_tarski(X3,X4)))=>(r2_hidden(k1_mcart_1(X1),X2)&(k2_mcart_1(X1)=X3|k2_mcart_1(X1)=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 0.13/0.38  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),k2_tarski(X3,X4)))=>(k1_mcart_1(X1)=X2&(k2_mcart_1(X1)=X3|k2_mcart_1(X1)=X4)))), inference(assume_negation,[status(cth)],[t18_mcart_1])).
% 0.13/0.38  fof(c_0_6, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.38  fof(c_0_7, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_8, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)))&((k2_mcart_1(esk2_0)!=esk4_0|k1_mcart_1(esk2_0)!=esk3_0)&(k2_mcart_1(esk2_0)!=esk5_0|k1_mcart_1(esk2_0)!=esk3_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.13/0.38  cnf(c_0_9, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_10, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  fof(c_0_11, plain, ![X13, X14, X15]:((r2_hidden(k1_mcart_1(X13),X14)|~r2_hidden(X13,k2_zfmisc_1(X14,X15)))&(r2_hidden(k2_mcart_1(X13),X15)|~r2_hidden(X13,k2_zfmisc_1(X14,X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.13/0.38  cnf(c_0_12, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_13, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.38  cnf(c_0_14, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk3_0),k2_tarski(esk4_0,esk5_0)))), inference(rw,[status(thm)],[c_0_12, c_0_10])).
% 0.13/0.38  fof(c_0_16, plain, ![X16, X17, X18, X19]:((r2_hidden(k1_mcart_1(X16),X17)|~r2_hidden(X16,k2_zfmisc_1(X17,k2_tarski(X18,X19))))&(k2_mcart_1(X16)=X18|k2_mcart_1(X16)=X19|~r2_hidden(X16,k2_zfmisc_1(X17,k2_tarski(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_mcart_1])])])).
% 0.13/0.38  cnf(c_0_17, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (r2_hidden(k1_mcart_1(esk2_0),k2_tarski(esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.38  cnf(c_0_19, plain, (k2_mcart_1(X1)=X2|k2_mcart_1(X1)=X3|~r2_hidden(X1,k2_zfmisc_1(X4,k2_tarski(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (k2_mcart_1(esk2_0)!=esk5_0|k1_mcart_1(esk2_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (k1_mcart_1(esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (k2_mcart_1(esk2_0)!=esk4_0|k1_mcart_1(esk2_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (k2_mcart_1(esk2_0)=esk5_0|k2_mcart_1(esk2_0)=esk4_0), inference(spm,[status(thm)],[c_0_19, c_0_15])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (k2_mcart_1(esk2_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21])])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (k2_mcart_1(esk2_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_21])])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_23, c_0_24]), c_0_25]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 27
% 0.13/0.38  # Proof object clause steps            : 16
% 0.13/0.38  # Proof object formula steps           : 11
% 0.13/0.38  # Proof object conjectures             : 13
% 0.13/0.38  # Proof object clause conjectures      : 10
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 7
% 0.13/0.38  # Proof object initial formulas used   : 5
% 0.13/0.38  # Proof object generating inferences   : 3
% 0.13/0.38  # Proof object simplifying inferences  : 9
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 5
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 12
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 11
% 0.13/0.38  # Processed clauses                    : 25
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 2
% 0.13/0.38  # ...remaining for further processing  : 22
% 0.13/0.38  # Other redundant clauses eliminated   : 3
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 3
% 0.13/0.38  # Generated clauses                    : 41
% 0.13/0.38  # ...of the previous two non-trivial   : 43
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 36
% 0.13/0.38  # Factorizations                       : 1
% 0.13/0.38  # Equation resolutions                 : 3
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 15
% 0.13/0.38  #    Positive orientable unit clauses  : 4
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 8
% 0.13/0.38  # Current number of unprocessed clauses: 29
% 0.13/0.38  # ...number of literals in the above   : 106
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 6
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 9
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 9
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.38  # Unit Clause-clause subsumption calls : 11
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 5
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 1070
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.027 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.032 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
