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
% DateTime   : Thu Dec  3 10:46:58 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   30 (  37 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    7 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 (  81 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(t63_subset_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(t55_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ( X1 != k1_xboole_0
       => m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(c_0_7,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X9,X8)
        | r2_hidden(X9,X8)
        | v1_xboole_0(X8) )
      & ( ~ r2_hidden(X9,X8)
        | m1_subset_1(X9,X8)
        | v1_xboole_0(X8) )
      & ( ~ m1_subset_1(X9,X8)
        | v1_xboole_0(X9)
        | ~ v1_xboole_0(X8) )
      & ( ~ v1_xboole_0(X9)
        | m1_subset_1(X9,X8)
        | ~ v1_xboole_0(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_8,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | ~ v1_xboole_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    inference(assume_negation,[status(cth)],[t63_subset_1])).

cnf(c_0_10,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    & ~ m1_subset_1(k1_tarski(esk1_0),k1_zfmisc_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_13,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,X14)
      | X14 = k1_xboole_0
      | m1_subset_1(k1_tarski(X15),k1_zfmisc_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | ~ r2_hidden(X12,X11)
      | r2_hidden(X12,X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_17,plain,(
    ! [X13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_18,negated_conjecture,
    ( ~ m1_subset_1(k1_tarski(esk1_0),k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

fof(c_0_24,plain,(
    ! [X6,X7] : ~ r2_hidden(X6,k2_zfmisc_1(X6,X7)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_15,c_0_23])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_27,c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:58:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.18/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.027 s
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.18/0.36  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 0.18/0.36  fof(t63_subset_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.18/0.36  fof(t55_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 0.18/0.36  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.18/0.36  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.18/0.36  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.18/0.36  fof(c_0_7, plain, ![X8, X9]:(((~m1_subset_1(X9,X8)|r2_hidden(X9,X8)|v1_xboole_0(X8))&(~r2_hidden(X9,X8)|m1_subset_1(X9,X8)|v1_xboole_0(X8)))&((~m1_subset_1(X9,X8)|v1_xboole_0(X9)|~v1_xboole_0(X8))&(~v1_xboole_0(X9)|m1_subset_1(X9,X8)|~v1_xboole_0(X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.18/0.36  fof(c_0_8, plain, ![X4, X5]:(~r2_hidden(X4,X5)|~v1_xboole_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 0.18/0.36  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)))), inference(assume_negation,[status(cth)],[t63_subset_1])).
% 0.18/0.36  cnf(c_0_10, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.36  cnf(c_0_11, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  fof(c_0_12, negated_conjecture, (r2_hidden(esk1_0,esk2_0)&~m1_subset_1(k1_tarski(esk1_0),k1_zfmisc_1(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.18/0.36  fof(c_0_13, plain, ![X14, X15]:(~m1_subset_1(X15,X14)|(X14=k1_xboole_0|m1_subset_1(k1_tarski(X15),k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).
% 0.18/0.36  cnf(c_0_14, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_10, c_0_11])).
% 0.18/0.36  cnf(c_0_15, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  fof(c_0_16, plain, ![X10, X11, X12]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|(~r2_hidden(X12,X11)|r2_hidden(X12,X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.18/0.36  fof(c_0_17, plain, ![X13]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.18/0.36  cnf(c_0_18, negated_conjecture, (~m1_subset_1(k1_tarski(esk1_0),k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_19, plain, (X2=k1_xboole_0|m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.36  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.18/0.36  cnf(c_0_21, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  cnf(c_0_22, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.36  cnf(c_0_23, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.18/0.36  fof(c_0_24, plain, ![X6, X7]:~r2_hidden(X6,k2_zfmisc_1(X6,X7)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.18/0.36  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.36  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_15, c_0_23])).
% 0.18/0.36  cnf(c_0_27, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.36  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_0,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.36  cnf(c_0_29, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_27, c_0_28]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 30
% 0.18/0.36  # Proof object clause steps            : 15
% 0.18/0.36  # Proof object formula steps           : 15
% 0.18/0.36  # Proof object conjectures             : 10
% 0.18/0.36  # Proof object clause conjectures      : 7
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 8
% 0.18/0.36  # Proof object initial formulas used   : 7
% 0.18/0.36  # Proof object generating inferences   : 5
% 0.18/0.36  # Proof object simplifying inferences  : 4
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 7
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 11
% 0.18/0.36  # Removed in clause preprocessing      : 0
% 0.18/0.36  # Initial clauses in saturation        : 11
% 0.18/0.36  # Processed clauses                    : 24
% 0.18/0.36  # ...of these trivial                  : 0
% 0.18/0.36  # ...subsumed                          : 2
% 0.18/0.36  # ...remaining for further processing  : 22
% 0.18/0.36  # Other redundant clauses eliminated   : 0
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 5
% 0.18/0.36  # Generated clauses                    : 20
% 0.18/0.36  # ...of the previous two non-trivial   : 17
% 0.18/0.36  # Contextual simplify-reflections      : 1
% 0.18/0.36  # Paramodulations                      : 20
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 0
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 17
% 0.18/0.36  #    Positive orientable unit clauses  : 4
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 3
% 0.18/0.36  #    Non-unit-clauses                  : 10
% 0.18/0.36  # Current number of unprocessed clauses: 3
% 0.18/0.36  # ...number of literals in the above   : 10
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 5
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 4
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 3
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.18/0.36  # Unit Clause-clause subsumption calls : 5
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 2
% 0.18/0.36  # BW rewrite match successes           : 2
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 846
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.026 s
% 0.18/0.36  # System time              : 0.005 s
% 0.18/0.36  # Total time               : 0.031 s
% 0.18/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
