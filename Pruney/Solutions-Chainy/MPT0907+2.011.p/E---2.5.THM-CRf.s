%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:07 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   29 (  80 expanded)
%              Number of clauses        :   16 (  34 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 ( 193 expanded)
%              Number of equality atoms :   35 ( 109 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(t66_mcart_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) != k1_xboole_0
     => ! [X3] :
          ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
         => ( X3 != k1_mcart_1(X3)
            & X3 != k2_mcart_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_mcart_1)).

fof(t48_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r2_hidden(X3,X2) )
     => k2_xboole_0(k2_tarski(X1,X3),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t67_mcart_1])).

fof(c_0_7,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | m1_subset_1(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_8,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0))
    & ( esk1_0 = k1_mcart_1(esk1_0)
      | esk1_0 = k2_mcart_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X14,X15,X16] :
      ( ( X16 != k1_mcart_1(X16)
        | ~ m1_subset_1(X16,k2_zfmisc_1(X14,X15))
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 )
      & ( X16 != k2_mcart_1(X16)
        | ~ m1_subset_1(X16,k2_zfmisc_1(X14,X15))
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_mcart_1])])])])).

cnf(c_0_10,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k2_zfmisc_1(X2,X3) = k1_xboole_0
    | X1 != k2_mcart_1(X1)
    | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk1_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( k2_zfmisc_1(X2,X3) = k1_xboole_0
    | X1 != k1_mcart_1(X1)
    | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | k2_mcart_1(esk1_0) != esk1_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( esk1_0 = k1_mcart_1(esk1_0)
    | esk1_0 = k2_mcart_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | k1_mcart_1(esk1_0) != esk1_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

fof(c_0_18,plain,(
    ! [X7,X8,X9] :
      ( ~ r2_hidden(X7,X8)
      | ~ r2_hidden(X9,X8)
      | k2_xboole_0(k2_tarski(X7,X9),X8) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_zfmisc_1])])).

cnf(c_0_19,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

fof(c_0_20,plain,(
    ! [X10,X11] : k2_xboole_0(k1_tarski(X10),X11) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X6] : k2_tarski(X6,X6) = k1_tarski(X6) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_22,plain,
    ( k2_xboole_0(k2_tarski(X1,X3),X2) = X2
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk1_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_19])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k2_xboole_0(k2_tarski(X1,esk1_0),k1_xboole_0) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_23]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:04:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.14/0.38  # and selection function SelectDiffNegLit.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.033 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t67_mcart_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_mcart_1)).
% 0.14/0.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.14/0.38  fof(t66_mcart_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)!=k1_xboole_0=>![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>(X3!=k1_mcart_1(X3)&X3!=k2_mcart_1(X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_mcart_1)).
% 0.14/0.38  fof(t48_zfmisc_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k2_xboole_0(k2_tarski(X1,X3),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 0.14/0.38  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.14/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.38  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t67_mcart_1])).
% 0.14/0.38  fof(c_0_7, plain, ![X12, X13]:(~r2_hidden(X12,X13)|m1_subset_1(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.14/0.38  fof(c_0_8, negated_conjecture, (r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0))&(esk1_0=k1_mcart_1(esk1_0)|esk1_0=k2_mcart_1(esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.14/0.38  fof(c_0_9, plain, ![X14, X15, X16]:((X16!=k1_mcart_1(X16)|~m1_subset_1(X16,k2_zfmisc_1(X14,X15))|k2_zfmisc_1(X14,X15)=k1_xboole_0)&(X16!=k2_mcart_1(X16)|~m1_subset_1(X16,k2_zfmisc_1(X14,X15))|k2_zfmisc_1(X14,X15)=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_mcart_1])])])])).
% 0.14/0.38  cnf(c_0_10, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_11, negated_conjecture, (r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_12, plain, (k2_zfmisc_1(X2,X3)=k1_xboole_0|X1!=k2_mcart_1(X1)|~m1_subset_1(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk1_0,k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.14/0.38  cnf(c_0_14, plain, (k2_zfmisc_1(X2,X3)=k1_xboole_0|X1!=k1_mcart_1(X1)|~m1_subset_1(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|k2_mcart_1(esk1_0)!=esk1_0), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (esk1_0=k1_mcart_1(esk1_0)|esk1_0=k2_mcart_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|k1_mcart_1(esk1_0)!=esk1_0), inference(spm,[status(thm)],[c_0_14, c_0_13])).
% 0.14/0.38  fof(c_0_18, plain, ![X7, X8, X9]:(~r2_hidden(X7,X8)|~r2_hidden(X9,X8)|k2_xboole_0(k2_tarski(X7,X9),X8)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_zfmisc_1])])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.14/0.38  fof(c_0_20, plain, ![X10, X11]:k2_xboole_0(k1_tarski(X10),X11)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.14/0.38  fof(c_0_21, plain, ![X6]:k2_tarski(X6,X6)=k1_tarski(X6), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.38  cnf(c_0_22, plain, (k2_xboole_0(k2_tarski(X1,X3),X2)=X2|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(esk1_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_11, c_0_19])).
% 0.14/0.38  cnf(c_0_24, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (k2_xboole_0(k2_tarski(X1,esk1_0),k1_xboole_0)=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.38  cnf(c_0_27, plain, (k2_xboole_0(k2_tarski(X1,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_23]), c_0_27]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 29
% 0.14/0.38  # Proof object clause steps            : 16
% 0.14/0.38  # Proof object formula steps           : 13
% 0.14/0.38  # Proof object conjectures             : 12
% 0.14/0.38  # Proof object clause conjectures      : 9
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 8
% 0.14/0.38  # Proof object initial formulas used   : 6
% 0.14/0.38  # Proof object generating inferences   : 6
% 0.14/0.38  # Proof object simplifying inferences  : 4
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 7
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 9
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 8
% 0.14/0.38  # Processed clauses                    : 24
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 24
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 4
% 0.14/0.38  # Generated clauses                    : 9
% 0.14/0.38  # ...of the previous two non-trivial   : 9
% 0.14/0.38  # Contextual simplify-reflections      : 1
% 0.14/0.38  # Paramodulations                      : 9
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 12
% 0.14/0.38  #    Positive orientable unit clauses  : 4
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 6
% 0.14/0.38  # Current number of unprocessed clauses: 0
% 0.14/0.38  # ...number of literals in the above   : 0
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 13
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 8
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 8
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.38  # Unit Clause-clause subsumption calls : 6
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 678
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.035 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.038 s
% 0.14/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
