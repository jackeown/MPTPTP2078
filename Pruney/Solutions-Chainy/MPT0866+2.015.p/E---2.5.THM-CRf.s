%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:32 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  40 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 ( 103 expanded)
%              Number of equality atoms :   19 (  49 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_mcart_1,conjecture,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ! [X3] :
              ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
             => X3 = k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc10_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & ~ ! [X3] :
                ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
               => X3 = k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t24_mcart_1])).

fof(c_0_7,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | ~ r2_hidden(X11,X12)
      | X11 = k4_tarski(k1_mcart_1(X11),k2_mcart_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_8,plain,(
    ! [X9,X10] : v1_relat_1(k2_zfmisc_1(X9,X10)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_9,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X7,X8)
      | v1_xboole_0(X8)
      | r2_hidden(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_10,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & m1_subset_1(esk3_0,k2_zfmisc_1(esk1_0,esk2_0))
    & esk3_0 != k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X5,X6] :
      ( v1_xboole_0(X5)
      | v1_xboole_0(X6)
      | ~ v1_xboole_0(k2_zfmisc_1(X5,X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc10_subset_1])])])).

cnf(c_0_16,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(esk1_0,esk2_0))
    | v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 != k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( v1_xboole_0(esk1_0)
    | v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( v1_xboole_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_26,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_25]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:02:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.19/0.37  # and selection function SelectSmallestOrientable.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t24_mcart_1, conjecture, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~(![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>X3=k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 0.19/0.37  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 0.19/0.37  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.37  fof(fc10_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>~(v1_xboole_0(k2_zfmisc_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_subset_1)).
% 0.19/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.37  fof(c_0_6, negated_conjecture, ~(![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~(![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>X3=k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3))))))), inference(assume_negation,[status(cth)],[t24_mcart_1])).
% 0.19/0.37  fof(c_0_7, plain, ![X11, X12]:(~v1_relat_1(X12)|(~r2_hidden(X11,X12)|X11=k4_tarski(k1_mcart_1(X11),k2_mcart_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 0.19/0.37  fof(c_0_8, plain, ![X9, X10]:v1_relat_1(k2_zfmisc_1(X9,X10)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.37  fof(c_0_9, plain, ![X7, X8]:(~m1_subset_1(X7,X8)|(v1_xboole_0(X8)|r2_hidden(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.37  fof(c_0_10, negated_conjecture, ((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&(m1_subset_1(esk3_0,k2_zfmisc_1(esk1_0,esk2_0))&esk3_0!=k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.19/0.37  cnf(c_0_11, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_12, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_13, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_0,k2_zfmisc_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  fof(c_0_15, plain, ![X5, X6]:(v1_xboole_0(X5)|v1_xboole_0(X6)|~v1_xboole_0(k2_zfmisc_1(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc10_subset_1])])])).
% 0.19/0.37  cnf(c_0_16, plain, (k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(esk1_0,esk2_0))|v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (esk3_0!=k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  fof(c_0_19, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.37  cnf(c_0_20, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_xboole_0(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.19/0.37  cnf(c_0_22, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (v1_xboole_0(esk1_0)|v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (v1_xboole_0(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_25]), c_0_26]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 28
% 0.19/0.37  # Proof object clause steps            : 15
% 0.19/0.37  # Proof object formula steps           : 13
% 0.19/0.37  # Proof object conjectures             : 12
% 0.19/0.37  # Proof object clause conjectures      : 9
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 9
% 0.19/0.37  # Proof object initial formulas used   : 6
% 0.19/0.37  # Proof object generating inferences   : 6
% 0.19/0.37  # Proof object simplifying inferences  : 3
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 6
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 9
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 9
% 0.19/0.37  # Processed clauses                    : 25
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 25
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 4
% 0.19/0.37  # Generated clauses                    : 11
% 0.19/0.37  # ...of the previous two non-trivial   : 12
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 11
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 12
% 0.19/0.37  #    Positive orientable unit clauses  : 4
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 3
% 0.19/0.37  #    Non-unit-clauses                  : 5
% 0.19/0.37  # Current number of unprocessed clauses: 5
% 0.19/0.37  # ...number of literals in the above   : 9
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 13
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 12
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 12
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 2
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 3
% 0.19/0.37  # BW rewrite match successes           : 3
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 648
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.026 s
% 0.19/0.37  # System time              : 0.005 s
% 0.19/0.37  # Total time               : 0.031 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
