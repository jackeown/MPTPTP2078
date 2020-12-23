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
% DateTime   : Thu Dec  3 10:56:44 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   19 (  49 expanded)
%              Number of clauses        :   12 (  17 expanded)
%              Number of leaves         :    3 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   74 ( 241 expanded)
%              Number of equality atoms :   15 (  45 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ~ ( v2_wellord1(X1)
          & k3_relat_1(X1) != k1_xboole_0
          & ! [X2] :
              ~ ( r2_hidden(X2,k3_relat_1(X1))
                & ! [X3] :
                    ( r2_hidden(X3,k3_relat_1(X1))
                   => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord1)).

fof(t10_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r1_tarski(X2,k3_relat_1(X1))
              & X2 != k1_xboole_0
              & ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ~ ( v2_wellord1(X1)
            & k3_relat_1(X1) != k1_xboole_0
            & ! [X2] :
                ~ ( r2_hidden(X2,k3_relat_1(X1))
                  & ! [X3] :
                      ( r2_hidden(X3,k3_relat_1(X1))
                     => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_wellord1])).

fof(c_0_4,negated_conjecture,(
    ! [X12] :
      ( v1_relat_1(esk2_0)
      & v2_wellord1(esk2_0)
      & k3_relat_1(esk2_0) != k1_xboole_0
      & ( r2_hidden(esk3_1(X12),k3_relat_1(esk2_0))
        | ~ r2_hidden(X12,k3_relat_1(esk2_0)) )
      & ( ~ r2_hidden(k4_tarski(X12,esk3_1(X12)),esk2_0)
        | ~ r2_hidden(X12,k3_relat_1(esk2_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

fof(c_0_5,plain,(
    ! [X7,X8,X10] :
      ( ( r2_hidden(esk1_2(X7,X8),X8)
        | ~ r1_tarski(X8,k3_relat_1(X7))
        | X8 = k1_xboole_0
        | ~ v2_wellord1(X7)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(X10,X8)
        | r2_hidden(k4_tarski(esk1_2(X7,X8),X10),X7)
        | ~ r1_tarski(X8,k3_relat_1(X7))
        | X8 = k1_xboole_0
        | ~ v2_wellord1(X7)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord1])])])])])).

fof(c_0_6,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_7,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk3_1(X1)),esk2_0)
    | ~ r2_hidden(X1,k3_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(esk1_2(X3,X2),X1),X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,k3_relat_1(X3))
    | ~ v2_wellord1(X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v2_wellord1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk1_2(esk2_0,X1),k3_relat_1(esk2_0))
    | ~ r2_hidden(esk3_1(esk1_2(esk2_0,X1)),X1)
    | ~ r1_tarski(X1,k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk3_1(X1),k3_relat_1(esk2_0))
    | ~ r2_hidden(X1,k3_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( k3_relat_1(esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk2_0,k3_relat_1(esk2_0)),k3_relat_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_9]),c_0_10]),c_0_14])]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:55:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.026 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t11_wellord1, conjecture, ![X1]:(v1_relat_1(X1)=>~(((v2_wellord1(X1)&k3_relat_1(X1)!=k1_xboole_0)&![X2]:~((r2_hidden(X2,k3_relat_1(X1))&![X3]:(r2_hidden(X3,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X3),X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord1)).
% 0.13/0.38  fof(t10_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~(((r1_tarski(X2,k3_relat_1(X1))&X2!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X2)&![X4]:(r2_hidden(X4,X2)=>r2_hidden(k4_tarski(X3,X4),X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord1)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(c_0_3, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>~(((v2_wellord1(X1)&k3_relat_1(X1)!=k1_xboole_0)&![X2]:~((r2_hidden(X2,k3_relat_1(X1))&![X3]:(r2_hidden(X3,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X3),X1)))))))), inference(assume_negation,[status(cth)],[t11_wellord1])).
% 0.13/0.38  fof(c_0_4, negated_conjecture, ![X12]:(v1_relat_1(esk2_0)&((v2_wellord1(esk2_0)&k3_relat_1(esk2_0)!=k1_xboole_0)&((r2_hidden(esk3_1(X12),k3_relat_1(esk2_0))|~r2_hidden(X12,k3_relat_1(esk2_0)))&(~r2_hidden(k4_tarski(X12,esk3_1(X12)),esk2_0)|~r2_hidden(X12,k3_relat_1(esk2_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).
% 0.13/0.38  fof(c_0_5, plain, ![X7, X8, X10]:((r2_hidden(esk1_2(X7,X8),X8)|(~r1_tarski(X8,k3_relat_1(X7))|X8=k1_xboole_0)|~v2_wellord1(X7)|~v1_relat_1(X7))&(~r2_hidden(X10,X8)|r2_hidden(k4_tarski(esk1_2(X7,X8),X10),X7)|(~r1_tarski(X8,k3_relat_1(X7))|X8=k1_xboole_0)|~v2_wellord1(X7)|~v1_relat_1(X7))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord1])])])])])).
% 0.13/0.38  fof(c_0_6, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  cnf(c_0_7, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk3_1(X1)),esk2_0)|~r2_hidden(X1,k3_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_8, plain, (r2_hidden(k4_tarski(esk1_2(X3,X2),X1),X3)|X2=k1_xboole_0|~r2_hidden(X1,X2)|~r1_tarski(X2,k3_relat_1(X3))|~v2_wellord1(X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_9, negated_conjecture, (v2_wellord1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_10, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_11, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_12, negated_conjecture, (X1=k1_xboole_0|~r2_hidden(esk1_2(esk2_0,X1),k3_relat_1(esk2_0))|~r2_hidden(esk3_1(esk1_2(esk2_0,X1)),X1)|~r1_tarski(X1,k3_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10])])).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (r2_hidden(esk3_1(X1),k3_relat_1(esk2_0))|~r2_hidden(X1,k3_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_14, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (k3_relat_1(esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (~r2_hidden(esk1_2(esk2_0,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])]), c_0_15])).
% 0.13/0.38  cnf(c_0_17, plain, (r2_hidden(esk1_2(X1,X2),X2)|X2=k1_xboole_0|~r1_tarski(X2,k3_relat_1(X1))|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_9]), c_0_10]), c_0_14])]), c_0_15]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 19
% 0.13/0.38  # Proof object clause steps            : 12
% 0.13/0.38  # Proof object formula steps           : 7
% 0.13/0.38  # Proof object conjectures             : 11
% 0.13/0.38  # Proof object clause conjectures      : 8
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 8
% 0.13/0.38  # Proof object initial formulas used   : 3
% 0.13/0.38  # Proof object generating inferences   : 3
% 0.13/0.38  # Proof object simplifying inferences  : 12
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 3
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 10
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 10
% 0.13/0.38  # Processed clauses                    : 13
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 13
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 5
% 0.13/0.38  # ...of the previous two non-trivial   : 3
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 3
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 11
% 0.20/0.38  #    Positive orientable unit clauses  : 3
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 6
% 0.20/0.38  # Current number of unprocessed clauses: 0
% 0.20/0.38  # ...number of literals in the above   : 0
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 0
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 6
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 2
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.38  # Unit Clause-clause subsumption calls : 1
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 0
% 0.20/0.38  # BW rewrite match successes           : 0
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 746
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.027 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.030 s
% 0.20/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
