%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:26 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   26 (  40 expanded)
%              Number of clauses        :   13 (  16 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  76 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t78_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(c_0_6,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k3_xboole_0(X7,k2_zfmisc_1(k1_relat_1(X7),k2_relat_1(X7))) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_relat_1])])).

fof(c_0_7,plain,(
    ! [X5,X6] : k1_setfam_1(k2_tarski(X5,X6)) = k3_xboole_0(X5,X6) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    inference(assume_negation,[status(cth)],[t78_relat_1])).

fof(c_0_9,plain,(
    ! [X3,X4] : r1_tarski(k3_xboole_0(X3,X4),X3) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_10,plain,
    ( k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) = X1
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(k1_relat_1(X8),k1_relat_1(X9))
        | ~ r1_tarski(X8,X9)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( r1_tarski(k2_relat_1(X8),k2_relat_1(X9))
        | ~ r1_tarski(X8,X9)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_13,c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | ~ r1_tarski(k1_relat_1(X11),X10)
      | k5_relat_1(k6_relat_1(X10),X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk1_0),k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_15])])).

cnf(c_0_24,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15])]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:24:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.35  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S070I
% 0.14/0.35  # and selection function SelectVGNonCR.
% 0.14/0.35  #
% 0.14/0.35  # Preprocessing time       : 0.012 s
% 0.14/0.35  # Presaturation interreduction done
% 0.14/0.35  
% 0.14/0.35  # Proof found!
% 0.14/0.35  # SZS status Theorem
% 0.14/0.35  # SZS output start CNFRefutation
% 0.14/0.35  fof(t22_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 0.14/0.35  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.35  fof(t78_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 0.14/0.35  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.14/0.35  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.14/0.35  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 0.14/0.35  fof(c_0_6, plain, ![X7]:(~v1_relat_1(X7)|k3_xboole_0(X7,k2_zfmisc_1(k1_relat_1(X7),k2_relat_1(X7)))=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_relat_1])])).
% 0.14/0.35  fof(c_0_7, plain, ![X5, X6]:k1_setfam_1(k2_tarski(X5,X6))=k3_xboole_0(X5,X6), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.35  fof(c_0_8, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1)), inference(assume_negation,[status(cth)],[t78_relat_1])).
% 0.14/0.35  fof(c_0_9, plain, ![X3, X4]:r1_tarski(k3_xboole_0(X3,X4),X3), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.14/0.35  cnf(c_0_10, plain, (k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.35  cnf(c_0_11, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.35  fof(c_0_12, negated_conjecture, (v1_relat_1(esk1_0)&k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0)!=esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.14/0.35  cnf(c_0_13, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.35  cnf(c_0_14, plain, (k1_setfam_1(k2_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))=X1|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.14/0.35  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.35  fof(c_0_16, plain, ![X8, X9]:((r1_tarski(k1_relat_1(X8),k1_relat_1(X9))|~r1_tarski(X8,X9)|~v1_relat_1(X9)|~v1_relat_1(X8))&(r1_tarski(k2_relat_1(X8),k2_relat_1(X9))|~r1_tarski(X8,X9)|~v1_relat_1(X9)|~v1_relat_1(X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.14/0.35  cnf(c_0_17, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_13, c_0_11])).
% 0.14/0.35  cnf(c_0_18, negated_conjecture, (k1_setfam_1(k2_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))=esk1_0), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.35  fof(c_0_19, plain, ![X10, X11]:(~v1_relat_1(X11)|(~r1_tarski(k1_relat_1(X11),X10)|k5_relat_1(k6_relat_1(X10),X11)=X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.14/0.35  cnf(c_0_20, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.35  cnf(c_0_21, negated_conjecture, (r1_tarski(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.35  cnf(c_0_22, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.35  cnf(c_0_23, negated_conjecture, (r1_tarski(k1_relat_1(esk1_0),k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_15])])).
% 0.14/0.35  cnf(c_0_24, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0)!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.35  cnf(c_0_25, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_15])]), c_0_24]), ['proof']).
% 0.14/0.35  # SZS output end CNFRefutation
% 0.14/0.35  # Proof object total steps             : 26
% 0.14/0.35  # Proof object clause steps            : 13
% 0.14/0.35  # Proof object formula steps           : 13
% 0.14/0.35  # Proof object conjectures             : 9
% 0.14/0.35  # Proof object clause conjectures      : 6
% 0.14/0.35  # Proof object formula conjectures     : 3
% 0.14/0.35  # Proof object initial clauses used    : 7
% 0.14/0.35  # Proof object initial formulas used   : 6
% 0.14/0.35  # Proof object generating inferences   : 4
% 0.14/0.35  # Proof object simplifying inferences  : 7
% 0.14/0.35  # Training examples: 0 positive, 0 negative
% 0.14/0.35  # Parsed axioms                        : 6
% 0.14/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.35  # Initial clauses                      : 8
% 0.14/0.35  # Removed in clause preprocessing      : 1
% 0.14/0.35  # Initial clauses in saturation        : 7
% 0.14/0.35  # Processed clauses                    : 16
% 0.14/0.35  # ...of these trivial                  : 0
% 0.14/0.35  # ...subsumed                          : 0
% 0.14/0.35  # ...remaining for further processing  : 16
% 0.14/0.35  # Other redundant clauses eliminated   : 0
% 0.14/0.35  # Clauses deleted for lack of memory   : 0
% 0.14/0.35  # Backward-subsumed                    : 0
% 0.14/0.35  # Backward-rewritten                   : 0
% 0.14/0.35  # Generated clauses                    : 6
% 0.14/0.35  # ...of the previous two non-trivial   : 5
% 0.14/0.35  # Contextual simplify-reflections      : 0
% 0.14/0.35  # Paramodulations                      : 6
% 0.14/0.35  # Factorizations                       : 0
% 0.14/0.35  # Equation resolutions                 : 0
% 0.14/0.35  # Propositional unsat checks           : 0
% 0.14/0.35  #    Propositional check models        : 0
% 0.14/0.35  #    Propositional check unsatisfiable : 0
% 0.14/0.35  #    Propositional clauses             : 0
% 0.14/0.35  #    Propositional clauses after purity: 0
% 0.14/0.35  #    Propositional unsat core size     : 0
% 0.14/0.35  #    Propositional preprocessing time  : 0.000
% 0.14/0.35  #    Propositional encoding time       : 0.000
% 0.14/0.35  #    Propositional solver time         : 0.000
% 0.14/0.35  #    Success case prop preproc time    : 0.000
% 0.14/0.35  #    Success case prop encoding time   : 0.000
% 0.14/0.35  #    Success case prop solver time     : 0.000
% 0.14/0.35  # Current number of processed clauses  : 9
% 0.14/0.35  #    Positive orientable unit clauses  : 5
% 0.14/0.35  #    Positive unorientable unit clauses: 0
% 0.14/0.35  #    Negative unit clauses             : 1
% 0.14/0.35  #    Non-unit-clauses                  : 3
% 0.14/0.35  # Current number of unprocessed clauses: 2
% 0.14/0.35  # ...number of literals in the above   : 7
% 0.14/0.35  # Current number of archived formulas  : 0
% 0.14/0.35  # Current number of archived clauses   : 8
% 0.14/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.35  # Unit Clause-clause subsumption calls : 0
% 0.14/0.35  # Rewrite failures with RHS unbound    : 0
% 0.14/0.35  # BW rewrite match attempts            : 0
% 0.14/0.35  # BW rewrite match successes           : 0
% 0.14/0.35  # Condensation attempts                : 0
% 0.14/0.35  # Condensation successes               : 0
% 0.14/0.35  # Termbank termtop insertions          : 642
% 0.14/0.35  
% 0.14/0.35  # -------------------------------------------------
% 0.14/0.35  # User time                : 0.011 s
% 0.14/0.35  # System time              : 0.004 s
% 0.14/0.35  # Total time               : 0.015 s
% 0.14/0.35  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
