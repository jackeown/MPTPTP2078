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
% DateTime   : Thu Dec  3 10:49:31 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   17 (  23 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  47 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t91_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t91_relat_1])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & k1_relat_1(k7_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | k1_relat_1(k7_relat_1(X8,X7)) = k3_xboole_0(k1_relat_1(X8),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_7,plain,(
    ! [X3,X4] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,X3) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_8,plain,(
    ! [X5,X6] :
      ( ~ r1_tarski(X5,X6)
      | k3_xboole_0(X5,X6) = X5 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_9,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( k3_xboole_0(esk1_0,k1_relat_1(esk2_0)) != esk1_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n012.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 16:30:07 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.18/0.34  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.18/0.34  # and selection function SelectCQIPrecWNTNp.
% 0.18/0.34  #
% 0.18/0.34  # Preprocessing time       : 0.026 s
% 0.18/0.34  # Presaturation interreduction done
% 0.18/0.34  
% 0.18/0.34  # Proof found!
% 0.18/0.34  # SZS status Theorem
% 0.18/0.34  # SZS output start CNFRefutation
% 0.18/0.34  fof(t91_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.18/0.34  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.18/0.34  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.18/0.34  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.18/0.34  fof(c_0_4, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1))), inference(assume_negation,[status(cth)],[t91_relat_1])).
% 0.18/0.34  fof(c_0_5, negated_conjecture, (v1_relat_1(esk2_0)&(r1_tarski(esk1_0,k1_relat_1(esk2_0))&k1_relat_1(k7_relat_1(esk2_0,esk1_0))!=esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.18/0.34  fof(c_0_6, plain, ![X7, X8]:(~v1_relat_1(X8)|k1_relat_1(k7_relat_1(X8,X7))=k3_xboole_0(k1_relat_1(X8),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.18/0.34  fof(c_0_7, plain, ![X3, X4]:k3_xboole_0(X3,X4)=k3_xboole_0(X4,X3), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.18/0.34  fof(c_0_8, plain, ![X5, X6]:(~r1_tarski(X5,X6)|k3_xboole_0(X5,X6)=X5), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.18/0.34  cnf(c_0_9, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk1_0))!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.18/0.34  cnf(c_0_10, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.34  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.18/0.34  cnf(c_0_12, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_13, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.34  cnf(c_0_14, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.18/0.34  cnf(c_0_15, negated_conjecture, (k3_xboole_0(esk1_0,k1_relat_1(esk2_0))!=esk1_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])]), c_0_12])).
% 0.18/0.34  cnf(c_0_16, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), ['proof']).
% 0.18/0.34  # SZS output end CNFRefutation
% 0.18/0.34  # Proof object total steps             : 17
% 0.18/0.34  # Proof object clause steps            : 8
% 0.18/0.34  # Proof object formula steps           : 9
% 0.18/0.34  # Proof object conjectures             : 8
% 0.18/0.34  # Proof object clause conjectures      : 5
% 0.18/0.34  # Proof object formula conjectures     : 3
% 0.18/0.34  # Proof object initial clauses used    : 6
% 0.18/0.34  # Proof object initial formulas used   : 4
% 0.18/0.34  # Proof object generating inferences   : 2
% 0.18/0.34  # Proof object simplifying inferences  : 4
% 0.18/0.34  # Training examples: 0 positive, 0 negative
% 0.18/0.34  # Parsed axioms                        : 4
% 0.18/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.34  # Initial clauses                      : 6
% 0.18/0.34  # Removed in clause preprocessing      : 0
% 0.18/0.34  # Initial clauses in saturation        : 6
% 0.18/0.34  # Processed clauses                    : 14
% 0.18/0.34  # ...of these trivial                  : 0
% 0.18/0.34  # ...subsumed                          : 0
% 0.18/0.34  # ...remaining for further processing  : 13
% 0.18/0.34  # Other redundant clauses eliminated   : 0
% 0.18/0.34  # Clauses deleted for lack of memory   : 0
% 0.18/0.34  # Backward-subsumed                    : 0
% 0.18/0.34  # Backward-rewritten                   : 0
% 0.18/0.34  # Generated clauses                    : 2
% 0.18/0.34  # ...of the previous two non-trivial   : 2
% 0.18/0.34  # Contextual simplify-reflections      : 0
% 0.18/0.34  # Paramodulations                      : 2
% 0.18/0.34  # Factorizations                       : 0
% 0.18/0.34  # Equation resolutions                 : 0
% 0.18/0.34  # Propositional unsat checks           : 0
% 0.18/0.34  #    Propositional check models        : 0
% 0.18/0.34  #    Propositional check unsatisfiable : 0
% 0.18/0.34  #    Propositional clauses             : 0
% 0.18/0.34  #    Propositional clauses after purity: 0
% 0.18/0.34  #    Propositional unsat core size     : 0
% 0.18/0.34  #    Propositional preprocessing time  : 0.000
% 0.18/0.34  #    Propositional encoding time       : 0.000
% 0.18/0.34  #    Propositional solver time         : 0.000
% 0.18/0.34  #    Success case prop preproc time    : 0.000
% 0.18/0.34  #    Success case prop encoding time   : 0.000
% 0.18/0.34  #    Success case prop solver time     : 0.000
% 0.18/0.34  # Current number of processed clauses  : 7
% 0.18/0.34  #    Positive orientable unit clauses  : 2
% 0.18/0.34  #    Positive unorientable unit clauses: 1
% 0.18/0.34  #    Negative unit clauses             : 2
% 0.18/0.34  #    Non-unit-clauses                  : 2
% 0.18/0.34  # Current number of unprocessed clauses: 0
% 0.18/0.34  # ...number of literals in the above   : 0
% 0.18/0.34  # Current number of archived formulas  : 0
% 0.18/0.34  # Current number of archived clauses   : 6
% 0.18/0.34  # Clause-clause subsumption calls (NU) : 0
% 0.18/0.34  # Rec. Clause-clause subsumption calls : 0
% 0.18/0.34  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.34  # Unit Clause-clause subsumption calls : 1
% 0.18/0.34  # Rewrite failures with RHS unbound    : 0
% 0.18/0.34  # BW rewrite match attempts            : 6
% 0.18/0.34  # BW rewrite match successes           : 6
% 0.18/0.34  # Condensation attempts                : 0
% 0.18/0.34  # Condensation successes               : 0
% 0.18/0.34  # Termbank termtop insertions          : 329
% 0.18/0.34  
% 0.18/0.34  # -------------------------------------------------
% 0.18/0.34  # User time                : 0.025 s
% 0.18/0.34  # System time              : 0.004 s
% 0.18/0.34  # Total time               : 0.029 s
% 0.18/0.34  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
