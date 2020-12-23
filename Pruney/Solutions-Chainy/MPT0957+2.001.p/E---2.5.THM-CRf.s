%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:46 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t30_wellord2,conjecture,(
    ! [X1] : r8_relat_2(k1_wellord2(X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord2)).

fof(d16_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> r8_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_2)).

fof(t3_wellord2,axiom,(
    ! [X1] : v8_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_wellord2)).

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
    ~ ! [X1] : r8_relat_2(k1_wellord2(X1),X1) ),
    inference(assume_negation,[status(cth)],[t30_wellord2])).

fof(c_0_8,plain,(
    ! [X5] :
      ( ( ~ v8_relat_2(X5)
        | r8_relat_2(X5,k3_relat_1(X5))
        | ~ v1_relat_1(X5) )
      & ( ~ r8_relat_2(X5,k3_relat_1(X5))
        | v8_relat_2(X5)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_2])])])).

fof(c_0_9,plain,(
    ! [X13] : v8_relat_2(k1_wellord2(X13)) ),
    inference(variable_rename,[status(thm)],[t3_wellord2])).

cnf(c_0_10,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_12,negated_conjecture,(
    ~ r8_relat_2(k1_wellord2(esk3_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_13,plain,
    ( r8_relat_2(X1,k3_relat_1(X1))
    | ~ v8_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v8_relat_2(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( ~ r8_relat_2(k1_wellord2(esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r8_relat_2(k1_wellord2(X1),X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_11])]),c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:02:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.21/0.39  # and selection function SelectDiffNegLit.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.027 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 0.21/0.39  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.21/0.39  fof(t30_wellord2, conjecture, ![X1]:r8_relat_2(k1_wellord2(X1),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_wellord2)).
% 0.21/0.39  fof(d16_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>(v8_relat_2(X1)<=>r8_relat_2(X1,k3_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_2)).
% 0.21/0.39  fof(t3_wellord2, axiom, ![X1]:v8_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_wellord2)).
% 0.21/0.39  fof(c_0_5, plain, ![X6, X7, X8, X9]:(((k3_relat_1(X7)=X6|X7!=k1_wellord2(X6)|~v1_relat_1(X7))&((~r2_hidden(k4_tarski(X8,X9),X7)|r1_tarski(X8,X9)|(~r2_hidden(X8,X6)|~r2_hidden(X9,X6))|X7!=k1_wellord2(X6)|~v1_relat_1(X7))&(~r1_tarski(X8,X9)|r2_hidden(k4_tarski(X8,X9),X7)|(~r2_hidden(X8,X6)|~r2_hidden(X9,X6))|X7!=k1_wellord2(X6)|~v1_relat_1(X7))))&(((r2_hidden(esk1_2(X6,X7),X6)|k3_relat_1(X7)!=X6|X7=k1_wellord2(X6)|~v1_relat_1(X7))&(r2_hidden(esk2_2(X6,X7),X6)|k3_relat_1(X7)!=X6|X7=k1_wellord2(X6)|~v1_relat_1(X7)))&((~r2_hidden(k4_tarski(esk1_2(X6,X7),esk2_2(X6,X7)),X7)|~r1_tarski(esk1_2(X6,X7),esk2_2(X6,X7))|k3_relat_1(X7)!=X6|X7=k1_wellord2(X6)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk1_2(X6,X7),esk2_2(X6,X7)),X7)|r1_tarski(esk1_2(X6,X7),esk2_2(X6,X7))|k3_relat_1(X7)!=X6|X7=k1_wellord2(X6)|~v1_relat_1(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.21/0.39  fof(c_0_6, plain, ![X12]:v1_relat_1(k1_wellord2(X12)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.21/0.39  fof(c_0_7, negated_conjecture, ~(![X1]:r8_relat_2(k1_wellord2(X1),X1)), inference(assume_negation,[status(cth)],[t30_wellord2])).
% 0.21/0.39  fof(c_0_8, plain, ![X5]:((~v8_relat_2(X5)|r8_relat_2(X5,k3_relat_1(X5))|~v1_relat_1(X5))&(~r8_relat_2(X5,k3_relat_1(X5))|v8_relat_2(X5)|~v1_relat_1(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_2])])])).
% 0.21/0.39  fof(c_0_9, plain, ![X13]:v8_relat_2(k1_wellord2(X13)), inference(variable_rename,[status(thm)],[t3_wellord2])).
% 0.21/0.39  cnf(c_0_10, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.39  cnf(c_0_11, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  fof(c_0_12, negated_conjecture, ~r8_relat_2(k1_wellord2(esk3_0),esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.21/0.39  cnf(c_0_13, plain, (r8_relat_2(X1,k3_relat_1(X1))|~v8_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.39  cnf(c_0_14, plain, (v8_relat_2(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_15, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]), c_0_11])])).
% 0.21/0.39  cnf(c_0_16, negated_conjecture, (~r8_relat_2(k1_wellord2(esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_17, plain, (r8_relat_2(k1_wellord2(X1),X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_11])]), c_0_15])).
% 0.21/0.39  cnf(c_0_18, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 19
% 0.21/0.39  # Proof object clause steps            : 8
% 0.21/0.39  # Proof object formula steps           : 11
% 0.21/0.39  # Proof object conjectures             : 5
% 0.21/0.39  # Proof object clause conjectures      : 2
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 5
% 0.21/0.39  # Proof object initial formulas used   : 5
% 0.21/0.39  # Proof object generating inferences   : 2
% 0.21/0.39  # Proof object simplifying inferences  : 7
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 5
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 12
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 12
% 0.21/0.39  # Processed clauses                    : 26
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 0
% 0.21/0.39  # ...remaining for further processing  : 26
% 0.21/0.39  # Other redundant clauses eliminated   : 3
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 1
% 0.21/0.39  # Generated clauses                    : 12
% 0.21/0.39  # ...of the previous two non-trivial   : 5
% 0.21/0.39  # Contextual simplify-reflections      : 0
% 0.21/0.39  # Paramodulations                      : 5
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 7
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 13
% 0.21/0.39  #    Positive orientable unit clauses  : 4
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 0
% 0.21/0.39  #    Non-unit-clauses                  : 9
% 0.21/0.39  # Current number of unprocessed clauses: 3
% 0.21/0.39  # ...number of literals in the above   : 10
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 13
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 12
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.39  # Unit Clause-clause subsumption calls : 3
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 1
% 0.21/0.39  # BW rewrite match successes           : 1
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 1142
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.024 s
% 0.21/0.39  # System time              : 0.007 s
% 0.21/0.39  # Total time               : 0.031 s
% 0.21/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
