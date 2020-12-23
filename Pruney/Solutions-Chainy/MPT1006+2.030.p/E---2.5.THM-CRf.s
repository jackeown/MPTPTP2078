%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:09 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   24 (  34 expanded)
%              Number of clauses        :   13 (  15 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 (  96 expanded)
%              Number of equality atoms :   23 (  42 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_xboole_0,X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
     => k8_relset_1(k1_xboole_0,X1,X3,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t47_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r1_tarski(k8_relset_1(X1,X2,X4,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_xboole_0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
       => k8_relset_1(k1_xboole_0,X1,X3,X2) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t60_funct_2])).

fof(c_0_6,plain,(
    ! [X8,X9] :
      ( ( k2_zfmisc_1(X8,X9) != k1_xboole_0
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X8,X9) = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X8,X9) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_7,plain,(
    ! [X10,X11,X12,X13] :
      ( ~ v1_funct_1(X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | r1_tarski(k8_relset_1(X10,X11,X13,X12),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_2])])).

fof(c_0_8,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,k1_xboole_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk1_0)))
    & k8_relset_1(k1_xboole_0,esk1_0,esk3_0,esk2_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_tarski(k8_relset_1(X2,X3,X1,X4),X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(k8_relset_1(X1,X2,esk3_0,X3),X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_18,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k8_relset_1(k1_xboole_0,X1,esk3_0,X2),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_13]),c_0_16])])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k8_relset_1(k1_xboole_0,esk1_0,esk3_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( k8_relset_1(k1_xboole_0,X1,esk3_0,X2) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.27  % Computer   : n005.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 12:25:17 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.28  # Version: 2.5pre002
% 0.08/0.28  # No SInE strategy applied
% 0.08/0.28  # Trying AutoSched0 for 299 seconds
% 0.12/0.31  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S076N
% 0.12/0.31  # and selection function SelectCQIAr.
% 0.12/0.31  #
% 0.12/0.31  # Preprocessing time       : 0.027 s
% 0.12/0.31  # Presaturation interreduction done
% 0.12/0.31  
% 0.12/0.31  # Proof found!
% 0.12/0.31  # SZS status Theorem
% 0.12/0.31  # SZS output start CNFRefutation
% 0.12/0.31  fof(t60_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_xboole_0,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))))=>k8_relset_1(k1_xboole_0,X1,X3,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 0.12/0.31  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.12/0.31  fof(t47_funct_2, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k8_relset_1(X1,X2,X4,X3),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_2)).
% 0.12/0.31  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.31  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.31  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_xboole_0,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))))=>k8_relset_1(k1_xboole_0,X1,X3,X2)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t60_funct_2])).
% 0.12/0.31  fof(c_0_6, plain, ![X8, X9]:((k2_zfmisc_1(X8,X9)!=k1_xboole_0|(X8=k1_xboole_0|X9=k1_xboole_0))&((X8!=k1_xboole_0|k2_zfmisc_1(X8,X9)=k1_xboole_0)&(X9!=k1_xboole_0|k2_zfmisc_1(X8,X9)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.12/0.31  fof(c_0_7, plain, ![X10, X11, X12, X13]:(~v1_funct_1(X13)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|r1_tarski(k8_relset_1(X10,X11,X13,X12),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_2])])).
% 0.12/0.31  fof(c_0_8, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,k1_xboole_0,esk1_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk1_0))))&k8_relset_1(k1_xboole_0,esk1_0,esk3_0,esk2_0)!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.12/0.31  cnf(c_0_9, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.31  cnf(c_0_10, plain, (r1_tarski(k8_relset_1(X2,X3,X1,X4),X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.31  cnf(c_0_11, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.31  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.31  cnf(c_0_13, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_9])).
% 0.12/0.31  fof(c_0_14, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.31  cnf(c_0_15, negated_conjecture, (r1_tarski(k8_relset_1(X1,X2,esk3_0,X3),X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.31  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.31  fof(c_0_17, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.31  cnf(c_0_18, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.31  cnf(c_0_19, negated_conjecture, (r1_tarski(k8_relset_1(k1_xboole_0,X1,esk3_0,X2),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_13]), c_0_16])])).
% 0.12/0.31  cnf(c_0_20, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.31  cnf(c_0_21, negated_conjecture, (k8_relset_1(k1_xboole_0,esk1_0,esk3_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.31  cnf(c_0_22, negated_conjecture, (k8_relset_1(k1_xboole_0,X1,esk3_0,X2)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.12/0.31  cnf(c_0_23, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22])]), ['proof']).
% 0.12/0.31  # SZS output end CNFRefutation
% 0.12/0.31  # Proof object total steps             : 24
% 0.12/0.31  # Proof object clause steps            : 13
% 0.12/0.31  # Proof object formula steps           : 11
% 0.12/0.31  # Proof object conjectures             : 11
% 0.12/0.31  # Proof object clause conjectures      : 8
% 0.12/0.31  # Proof object formula conjectures     : 3
% 0.12/0.31  # Proof object initial clauses used    : 7
% 0.12/0.31  # Proof object initial formulas used   : 5
% 0.12/0.31  # Proof object generating inferences   : 3
% 0.12/0.31  # Proof object simplifying inferences  : 8
% 0.12/0.31  # Training examples: 0 positive, 0 negative
% 0.12/0.31  # Parsed axioms                        : 5
% 0.12/0.31  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.31  # Initial clauses                      : 12
% 0.12/0.31  # Removed in clause preprocessing      : 0
% 0.12/0.31  # Initial clauses in saturation        : 12
% 0.12/0.31  # Processed clauses                    : 33
% 0.12/0.31  # ...of these trivial                  : 0
% 0.12/0.31  # ...subsumed                          : 0
% 0.12/0.31  # ...remaining for further processing  : 33
% 0.12/0.31  # Other redundant clauses eliminated   : 4
% 0.12/0.31  # Clauses deleted for lack of memory   : 0
% 0.12/0.31  # Backward-subsumed                    : 0
% 0.12/0.31  # Backward-rewritten                   : 4
% 0.12/0.31  # Generated clauses                    : 15
% 0.12/0.31  # ...of the previous two non-trivial   : 12
% 0.12/0.31  # Contextual simplify-reflections      : 0
% 0.12/0.31  # Paramodulations                      : 11
% 0.12/0.31  # Factorizations                       : 0
% 0.12/0.31  # Equation resolutions                 : 4
% 0.12/0.31  # Propositional unsat checks           : 0
% 0.12/0.31  #    Propositional check models        : 0
% 0.12/0.31  #    Propositional check unsatisfiable : 0
% 0.12/0.31  #    Propositional clauses             : 0
% 0.12/0.31  #    Propositional clauses after purity: 0
% 0.12/0.31  #    Propositional unsat core size     : 0
% 0.12/0.31  #    Propositional preprocessing time  : 0.000
% 0.12/0.31  #    Propositional encoding time       : 0.000
% 0.12/0.31  #    Propositional solver time         : 0.000
% 0.12/0.31  #    Success case prop preproc time    : 0.000
% 0.12/0.31  #    Success case prop encoding time   : 0.000
% 0.12/0.31  #    Success case prop solver time     : 0.000
% 0.12/0.31  # Current number of processed clauses  : 14
% 0.12/0.31  #    Positive orientable unit clauses  : 9
% 0.12/0.31  #    Positive unorientable unit clauses: 0
% 0.12/0.31  #    Negative unit clauses             : 0
% 0.12/0.31  #    Non-unit-clauses                  : 5
% 0.12/0.31  # Current number of unprocessed clauses: 2
% 0.12/0.31  # ...number of literals in the above   : 3
% 0.12/0.31  # Current number of archived formulas  : 0
% 0.12/0.31  # Current number of archived clauses   : 15
% 0.12/0.31  # Clause-clause subsumption calls (NU) : 2
% 0.12/0.31  # Rec. Clause-clause subsumption calls : 2
% 0.12/0.31  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.31  # Unit Clause-clause subsumption calls : 0
% 0.12/0.31  # Rewrite failures with RHS unbound    : 0
% 0.12/0.31  # BW rewrite match attempts            : 5
% 0.12/0.31  # BW rewrite match successes           : 4
% 0.12/0.31  # Condensation attempts                : 0
% 0.12/0.31  # Condensation successes               : 0
% 0.12/0.31  # Termbank termtop insertions          : 790
% 0.12/0.31  
% 0.12/0.31  # -------------------------------------------------
% 0.12/0.31  # User time                : 0.027 s
% 0.12/0.31  # System time              : 0.004 s
% 0.12/0.31  # Total time               : 0.031 s
% 0.12/0.31  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
