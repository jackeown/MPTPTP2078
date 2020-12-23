%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:39 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   58 (  58 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t150_relat_1,conjecture,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(c_0_7,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t150_relat_1])).

fof(c_0_9,plain,(
    ! [X11] : v1_relat_1(k6_relat_1(X11)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_10,plain,(
    ! [X9,X10] : ~ r2_hidden(X9,k2_zfmisc_1(X9,X10)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_11,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,(
    k9_relat_1(k1_xboole_0,esk3_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_13,plain,(
    ! [X5] :
      ( X5 = k1_xboole_0
      | r2_hidden(esk1_1(X5),X5) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_14,plain,(
    ! [X12,X13,X14,X16] :
      ( ( r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X14))
        | ~ r2_hidden(X12,k9_relat_1(X14,X13))
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk2_3(X12,X13,X14),X12),X14)
        | ~ r2_hidden(X12,k9_relat_1(X14,X13))
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk2_3(X12,X13,X14),X13)
        | ~ r2_hidden(X12,k9_relat_1(X14,X13))
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(X16,k1_relat_1(X14))
        | ~ r2_hidden(k4_tarski(X16,X12),X14)
        | ~ r2_hidden(X16,X13)
        | r2_hidden(X12,k9_relat_1(X14,X13))
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_15,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),k9_relat_1(k1_xboole_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_24,c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.06/0.25  % Computer   : n017.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 19:07:16 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.26  # Version: 2.5pre002
% 0.06/0.26  # No SInE strategy applied
% 0.06/0.26  # Trying AutoSched0 for 299 seconds
% 0.10/0.27  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EA
% 0.10/0.27  # and selection function SelectDivPreferIntoLits.
% 0.10/0.27  #
% 0.10/0.27  # Preprocessing time       : 0.012 s
% 0.10/0.27  # Presaturation interreduction done
% 0.10/0.27  
% 0.10/0.27  # Proof found!
% 0.10/0.27  # SZS status Theorem
% 0.10/0.27  # SZS output start CNFRefutation
% 0.10/0.27  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.10/0.27  fof(t150_relat_1, conjecture, ![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 0.10/0.27  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.10/0.27  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.10/0.27  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.10/0.27  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.10/0.27  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.10/0.27  fof(c_0_7, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.10/0.27  fof(c_0_8, negated_conjecture, ~(![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t150_relat_1])).
% 0.10/0.27  fof(c_0_9, plain, ![X11]:v1_relat_1(k6_relat_1(X11)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.10/0.27  fof(c_0_10, plain, ![X9, X10]:~r2_hidden(X9,k2_zfmisc_1(X9,X10)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.10/0.27  cnf(c_0_11, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.10/0.27  fof(c_0_12, negated_conjecture, k9_relat_1(k1_xboole_0,esk3_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.10/0.27  fof(c_0_13, plain, ![X5]:(X5=k1_xboole_0|r2_hidden(esk1_1(X5),X5)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.10/0.27  fof(c_0_14, plain, ![X12, X13, X14, X16]:((((r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X14))|~r2_hidden(X12,k9_relat_1(X14,X13))|~v1_relat_1(X14))&(r2_hidden(k4_tarski(esk2_3(X12,X13,X14),X12),X14)|~r2_hidden(X12,k9_relat_1(X14,X13))|~v1_relat_1(X14)))&(r2_hidden(esk2_3(X12,X13,X14),X13)|~r2_hidden(X12,k9_relat_1(X14,X13))|~v1_relat_1(X14)))&(~r2_hidden(X16,k1_relat_1(X14))|~r2_hidden(k4_tarski(X16,X12),X14)|~r2_hidden(X16,X13)|r2_hidden(X12,k9_relat_1(X14,X13))|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.10/0.27  cnf(c_0_15, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.10/0.27  cnf(c_0_16, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.10/0.27  cnf(c_0_17, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.10/0.27  cnf(c_0_18, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_11])).
% 0.10/0.27  cnf(c_0_19, negated_conjecture, (k9_relat_1(k1_xboole_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.27  cnf(c_0_20, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.10/0.27  cnf(c_0_21, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.10/0.27  cnf(c_0_22, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.10/0.27  cnf(c_0_23, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.10/0.27  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_1(k9_relat_1(k1_xboole_0,esk3_0)),k9_relat_1(k1_xboole_0,esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.10/0.27  cnf(c_0_25, plain, (~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.10/0.27  cnf(c_0_26, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_24, c_0_25]), ['proof']).
% 0.10/0.27  # SZS output end CNFRefutation
% 0.10/0.27  # Proof object total steps             : 27
% 0.10/0.27  # Proof object clause steps            : 13
% 0.10/0.27  # Proof object formula steps           : 14
% 0.10/0.27  # Proof object conjectures             : 6
% 0.10/0.27  # Proof object clause conjectures      : 3
% 0.10/0.27  # Proof object formula conjectures     : 3
% 0.10/0.27  # Proof object initial clauses used    : 7
% 0.10/0.27  # Proof object initial formulas used   : 7
% 0.10/0.27  # Proof object generating inferences   : 4
% 0.10/0.27  # Proof object simplifying inferences  : 3
% 0.10/0.27  # Training examples: 0 positive, 0 negative
% 0.10/0.27  # Parsed axioms                        : 7
% 0.10/0.27  # Removed by relevancy pruning/SinE    : 0
% 0.10/0.27  # Initial clauses                      : 12
% 0.10/0.27  # Removed in clause preprocessing      : 0
% 0.10/0.27  # Initial clauses in saturation        : 12
% 0.10/0.27  # Processed clauses                    : 44
% 0.10/0.27  # ...of these trivial                  : 1
% 0.10/0.27  # ...subsumed                          : 9
% 0.10/0.27  # ...remaining for further processing  : 34
% 0.10/0.27  # Other redundant clauses eliminated   : 3
% 0.10/0.27  # Clauses deleted for lack of memory   : 0
% 0.10/0.27  # Backward-subsumed                    : 0
% 0.10/0.27  # Backward-rewritten                   : 0
% 0.10/0.27  # Generated clauses                    : 67
% 0.10/0.27  # ...of the previous two non-trivial   : 53
% 0.10/0.27  # Contextual simplify-reflections      : 0
% 0.10/0.27  # Paramodulations                      : 62
% 0.10/0.27  # Factorizations                       : 0
% 0.10/0.27  # Equation resolutions                 : 3
% 0.10/0.27  # Propositional unsat checks           : 0
% 0.10/0.27  #    Propositional check models        : 0
% 0.10/0.27  #    Propositional check unsatisfiable : 0
% 0.10/0.27  #    Propositional clauses             : 0
% 0.10/0.27  #    Propositional clauses after purity: 0
% 0.10/0.27  #    Propositional unsat core size     : 0
% 0.10/0.27  #    Propositional preprocessing time  : 0.000
% 0.10/0.27  #    Propositional encoding time       : 0.000
% 0.10/0.27  #    Propositional solver time         : 0.000
% 0.10/0.27  #    Success case prop preproc time    : 0.000
% 0.10/0.27  #    Success case prop encoding time   : 0.000
% 0.10/0.27  #    Success case prop solver time     : 0.000
% 0.10/0.27  # Current number of processed clauses  : 18
% 0.10/0.27  #    Positive orientable unit clauses  : 5
% 0.10/0.27  #    Positive unorientable unit clauses: 0
% 0.10/0.27  #    Negative unit clauses             : 4
% 0.10/0.27  #    Non-unit-clauses                  : 9
% 0.10/0.27  # Current number of unprocessed clauses: 32
% 0.10/0.27  # ...number of literals in the above   : 78
% 0.10/0.27  # Current number of archived formulas  : 0
% 0.10/0.27  # Current number of archived clauses   : 14
% 0.10/0.27  # Clause-clause subsumption calls (NU) : 19
% 0.10/0.27  # Rec. Clause-clause subsumption calls : 19
% 0.10/0.27  # Non-unit clause-clause subsumptions  : 5
% 0.10/0.27  # Unit Clause-clause subsumption calls : 0
% 0.10/0.27  # Rewrite failures with RHS unbound    : 0
% 0.10/0.27  # BW rewrite match attempts            : 0
% 0.10/0.27  # BW rewrite match successes           : 0
% 0.10/0.27  # Condensation attempts                : 0
% 0.10/0.27  # Condensation successes               : 0
% 0.10/0.27  # Termbank termtop insertions          : 1326
% 0.10/0.27  
% 0.10/0.27  # -------------------------------------------------
% 0.10/0.27  # User time                : 0.011 s
% 0.10/0.27  # System time              : 0.003 s
% 0.10/0.27  # Total time               : 0.015 s
% 0.10/0.27  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
