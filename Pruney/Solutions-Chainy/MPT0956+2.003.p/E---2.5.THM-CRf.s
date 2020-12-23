%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:46 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   19 (  22 expanded)
%              Number of clauses        :    8 (   9 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   68 (  71 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t29_wellord2,conjecture,(
    ! [X1] : r1_relat_2(k1_wellord2(X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord2)).

fof(d9_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> r1_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_relat_2)).

fof(t2_wellord2,axiom,(
    ! [X1] : v1_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord2)).

fof(c_0_5,plain,(
    ! [X6,X7,X8,X9] :
      ( ( k3_relat_1(X7) = X6
        | X7 != k1_wellord2(X6)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(X8,X9),X7)
        | r1_tarski(X8,X9)
        | ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X9,X6)
        | X7 != k1_wellord2(X6)
        | ~ v1_relat_1(X7) )
      & ( ~ r1_tarski(X8,X9)
        | r2_hidden(k4_tarski(X8,X9),X7)
        | ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X9,X6)
        | X7 != k1_wellord2(X6)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk1_2(X6,X7),X6)
        | k3_relat_1(X7) != X6
        | X7 = k1_wellord2(X6)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk2_2(X6,X7),X6)
        | k3_relat_1(X7) != X6
        | X7 = k1_wellord2(X6)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X6,X7),esk2_2(X6,X7)),X7)
        | ~ r1_tarski(esk1_2(X6,X7),esk2_2(X6,X7))
        | k3_relat_1(X7) != X6
        | X7 = k1_wellord2(X6)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk1_2(X6,X7),esk2_2(X6,X7)),X7)
        | r1_tarski(esk1_2(X6,X7),esk2_2(X6,X7))
        | k3_relat_1(X7) != X6
        | X7 = k1_wellord2(X6)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_6,plain,(
    ! [X12] : v1_relat_1(k1_wellord2(X12)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] : r1_relat_2(k1_wellord2(X1),X1) ),
    inference(assume_negation,[status(cth)],[t29_wellord2])).

fof(c_0_8,plain,(
    ! [X5] :
      ( ( ~ v1_relat_2(X5)
        | r1_relat_2(X5,k3_relat_1(X5))
        | ~ v1_relat_1(X5) )
      & ( ~ r1_relat_2(X5,k3_relat_1(X5))
        | v1_relat_2(X5)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_relat_2])])])).

fof(c_0_9,plain,(
    ! [X13] : v1_relat_2(k1_wellord2(X13)) ),
    inference(variable_rename,[status(thm)],[t2_wellord2])).

cnf(c_0_10,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_12,negated_conjecture,(
    ~ r1_relat_2(k1_wellord2(esk3_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_13,plain,
    ( r1_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_relat_2(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_relat_2(k1_wellord2(esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_relat_2(k1_wellord2(X1),X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_11])]),c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.13/0.37  # and selection function SelectDiffNegLit.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.13/0.37  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.13/0.37  fof(t29_wellord2, conjecture, ![X1]:r1_relat_2(k1_wellord2(X1),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord2)).
% 0.13/0.37  fof(d9_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>(v1_relat_2(X1)<=>r1_relat_2(X1,k3_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_relat_2)).
% 0.13/0.37  fof(t2_wellord2, axiom, ![X1]:v1_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_wellord2)).
% 0.13/0.37  fof(c_0_5, plain, ![X6, X7, X8, X9]:(((k3_relat_1(X7)=X6|X7!=k1_wellord2(X6)|~v1_relat_1(X7))&((~r2_hidden(k4_tarski(X8,X9),X7)|r1_tarski(X8,X9)|(~r2_hidden(X8,X6)|~r2_hidden(X9,X6))|X7!=k1_wellord2(X6)|~v1_relat_1(X7))&(~r1_tarski(X8,X9)|r2_hidden(k4_tarski(X8,X9),X7)|(~r2_hidden(X8,X6)|~r2_hidden(X9,X6))|X7!=k1_wellord2(X6)|~v1_relat_1(X7))))&(((r2_hidden(esk1_2(X6,X7),X6)|k3_relat_1(X7)!=X6|X7=k1_wellord2(X6)|~v1_relat_1(X7))&(r2_hidden(esk2_2(X6,X7),X6)|k3_relat_1(X7)!=X6|X7=k1_wellord2(X6)|~v1_relat_1(X7)))&((~r2_hidden(k4_tarski(esk1_2(X6,X7),esk2_2(X6,X7)),X7)|~r1_tarski(esk1_2(X6,X7),esk2_2(X6,X7))|k3_relat_1(X7)!=X6|X7=k1_wellord2(X6)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk1_2(X6,X7),esk2_2(X6,X7)),X7)|r1_tarski(esk1_2(X6,X7),esk2_2(X6,X7))|k3_relat_1(X7)!=X6|X7=k1_wellord2(X6)|~v1_relat_1(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.13/0.37  fof(c_0_6, plain, ![X12]:v1_relat_1(k1_wellord2(X12)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.13/0.37  fof(c_0_7, negated_conjecture, ~(![X1]:r1_relat_2(k1_wellord2(X1),X1)), inference(assume_negation,[status(cth)],[t29_wellord2])).
% 0.13/0.37  fof(c_0_8, plain, ![X5]:((~v1_relat_2(X5)|r1_relat_2(X5,k3_relat_1(X5))|~v1_relat_1(X5))&(~r1_relat_2(X5,k3_relat_1(X5))|v1_relat_2(X5)|~v1_relat_1(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_relat_2])])])).
% 0.13/0.37  fof(c_0_9, plain, ![X13]:v1_relat_2(k1_wellord2(X13)), inference(variable_rename,[status(thm)],[t2_wellord2])).
% 0.13/0.37  cnf(c_0_10, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_11, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  fof(c_0_12, negated_conjecture, ~r1_relat_2(k1_wellord2(esk3_0),esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.13/0.37  cnf(c_0_13, plain, (r1_relat_2(X1,k3_relat_1(X1))|~v1_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_14, plain, (v1_relat_2(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_15, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]), c_0_11])])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (~r1_relat_2(k1_wellord2(esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_17, plain, (r1_relat_2(k1_wellord2(X1),X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_11])]), c_0_15])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 19
% 0.13/0.37  # Proof object clause steps            : 8
% 0.13/0.37  # Proof object formula steps           : 11
% 0.13/0.37  # Proof object conjectures             : 5
% 0.13/0.37  # Proof object clause conjectures      : 2
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 5
% 0.13/0.37  # Proof object initial formulas used   : 5
% 0.13/0.37  # Proof object generating inferences   : 2
% 0.13/0.37  # Proof object simplifying inferences  : 7
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 5
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 12
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 12
% 0.13/0.37  # Processed clauses                    : 26
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 26
% 0.13/0.37  # Other redundant clauses eliminated   : 3
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 1
% 0.13/0.37  # Generated clauses                    : 12
% 0.13/0.37  # ...of the previous two non-trivial   : 5
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 5
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 7
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 13
% 0.13/0.37  #    Positive orientable unit clauses  : 4
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 0
% 0.13/0.37  #    Non-unit-clauses                  : 9
% 0.13/0.37  # Current number of unprocessed clauses: 3
% 0.13/0.37  # ...number of literals in the above   : 10
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 13
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 12
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 3
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 1
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1142
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.025 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
