%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:11 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  37 expanded)
%              Number of clauses        :   13 (  15 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 109 expanded)
%              Number of equality atoms :    7 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ~ ( X2 != k1_xboole_0
          & ! [X3] :
              ( m1_subset_1(X3,X1)
             => ~ r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

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

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ~ ( X2 != k1_xboole_0
            & ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t10_subset_1])).

fof(c_0_6,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | ~ r2_hidden(X12,X11)
      | r2_hidden(X12,X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_7,negated_conjecture,(
    ! [X15] :
      ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
      & esk3_0 != k1_xboole_0
      & ( ~ m1_subset_1(X15,esk2_0)
        | ~ r2_hidden(X15,esk3_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

fof(c_0_8,plain,(
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

fof(c_0_9,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ v1_xboole_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_10,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X4] :
      ( X4 = k1_xboole_0
      | r2_hidden(esk1_1(X4),X4) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_1(esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( ~ m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(esk1_1(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.20/0.39  # and selection function SelectNewComplexAHPNS.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.043 s
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t10_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~((X2!=k1_xboole_0&![X3]:(m1_subset_1(X3,X1)=>~(r2_hidden(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 0.20/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.39  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.39  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 0.20/0.39  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.39  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>~((X2!=k1_xboole_0&![X3]:(m1_subset_1(X3,X1)=>~(r2_hidden(X3,X2))))))), inference(assume_negation,[status(cth)],[t10_subset_1])).
% 0.20/0.39  fof(c_0_6, plain, ![X10, X11, X12]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|(~r2_hidden(X12,X11)|r2_hidden(X12,X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.39  fof(c_0_7, negated_conjecture, ![X15]:(m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(esk3_0!=k1_xboole_0&(~m1_subset_1(X15,esk2_0)|~r2_hidden(X15,esk3_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).
% 0.20/0.39  fof(c_0_8, plain, ![X8, X9]:(((~m1_subset_1(X9,X8)|r2_hidden(X9,X8)|v1_xboole_0(X8))&(~r2_hidden(X9,X8)|m1_subset_1(X9,X8)|v1_xboole_0(X8)))&((~m1_subset_1(X9,X8)|v1_xboole_0(X9)|~v1_xboole_0(X8))&(~v1_xboole_0(X9)|m1_subset_1(X9,X8)|~v1_xboole_0(X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.39  fof(c_0_9, plain, ![X6, X7]:(~r2_hidden(X6,X7)|~v1_xboole_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 0.20/0.39  cnf(c_0_10, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.39  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  fof(c_0_12, plain, ![X4]:(X4=k1_xboole_0|r2_hidden(esk1_1(X4),X4)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.39  cnf(c_0_13, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_14, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_15, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.39  cnf(c_0_16, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_17, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_18, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.39  cnf(c_0_19, negated_conjecture, (r2_hidden(esk1_1(esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (~m1_subset_1(X1,esk2_0)|~r2_hidden(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (~r2_hidden(esk1_1(esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.39  cnf(c_0_23, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_16]), c_0_17]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 24
% 0.20/0.39  # Proof object clause steps            : 13
% 0.20/0.39  # Proof object formula steps           : 11
% 0.20/0.39  # Proof object conjectures             : 11
% 0.20/0.39  # Proof object clause conjectures      : 8
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 7
% 0.20/0.39  # Proof object initial formulas used   : 5
% 0.20/0.39  # Proof object generating inferences   : 5
% 0.20/0.39  # Proof object simplifying inferences  : 3
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 5
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 10
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 10
% 0.20/0.39  # Processed clauses                    : 21
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 0
% 0.20/0.39  # ...remaining for further processing  : 21
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 22
% 0.20/0.39  # ...of the previous two non-trivial   : 16
% 0.20/0.39  # Contextual simplify-reflections      : 1
% 0.20/0.39  # Paramodulations                      : 22
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 21
% 0.20/0.39  #    Positive orientable unit clauses  : 3
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 3
% 0.20/0.39  #    Non-unit-clauses                  : 15
% 0.20/0.39  # Current number of unprocessed clauses: 5
% 0.20/0.39  # ...number of literals in the above   : 15
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 0
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 9
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 7
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.39  # Unit Clause-clause subsumption calls : 2
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 0
% 0.20/0.39  # BW rewrite match successes           : 0
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 866
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.044 s
% 0.20/0.39  # System time              : 0.003 s
% 0.20/0.39  # Total time               : 0.047 s
% 0.20/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
