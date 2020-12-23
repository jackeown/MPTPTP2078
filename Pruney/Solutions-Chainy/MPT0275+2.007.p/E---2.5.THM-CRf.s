%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:01 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  63 expanded)
%              Number of clauses        :   17 (  28 expanded)
%              Number of leaves         :    3 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 ( 196 expanded)
%              Number of equality atoms :   15 (  52 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t73_zfmisc_1])).

fof(c_0_4,plain,(
    ! [X20,X21] :
      ( ( k4_xboole_0(X20,X21) != k1_xboole_0
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | k4_xboole_0(X20,X21) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

fof(c_0_5,negated_conjecture,
    ( ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0
      | ~ r2_hidden(esk3_0,esk5_0)
      | ~ r2_hidden(esk4_0,esk5_0) )
    & ( r2_hidden(esk3_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 )
    & ( r2_hidden(esk4_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

fof(c_0_6,plain,(
    ! [X36,X37,X38] :
      ( ( r2_hidden(X36,X38)
        | ~ r1_tarski(k2_tarski(X36,X37),X38) )
      & ( r2_hidden(X37,X38)
        | ~ r1_tarski(k2_tarski(X36,X37),X38) )
      & ( ~ r2_hidden(X36,X38)
        | ~ r2_hidden(X37,X38)
        | r1_tarski(k2_tarski(X36,X37),X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_7,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0)
    | r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(k2_tarski(X1,esk4_0),esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_13])])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_18])])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4b
% 0.20/0.38  # and selection function SelectCQIPrecW.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t73_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 0.20/0.38  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 0.20/0.38  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.20/0.38  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3)))), inference(assume_negation,[status(cth)],[t73_zfmisc_1])).
% 0.20/0.38  fof(c_0_4, plain, ![X20, X21]:((k4_xboole_0(X20,X21)!=k1_xboole_0|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|k4_xboole_0(X20,X21)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 0.20/0.38  fof(c_0_5, negated_conjecture, ((k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0|(~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)))&((r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0)&(r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).
% 0.20/0.38  fof(c_0_6, plain, ![X36, X37, X38]:(((r2_hidden(X36,X38)|~r1_tarski(k2_tarski(X36,X37),X38))&(r2_hidden(X37,X38)|~r1_tarski(k2_tarski(X36,X37),X38)))&(~r2_hidden(X36,X38)|~r2_hidden(X37,X38)|r1_tarski(k2_tarski(X36,X37),X38))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.20/0.38  cnf(c_0_7, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  cnf(c_0_8, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_9, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_10, negated_conjecture, (r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0)|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.20/0.38  cnf(c_0_11, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_12, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_13, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.38  cnf(c_0_14, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0)|r2_hidden(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_7, c_0_11])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0|~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (r1_tarski(k2_tarski(X1,esk4_0),esk5_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0|~r2_hidden(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_13])])).
% 0.20/0.38  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (r1_tarski(k2_tarski(esk3_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_18])])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 24
% 0.20/0.38  # Proof object clause steps            : 17
% 0.20/0.38  # Proof object formula steps           : 7
% 0.20/0.38  # Proof object conjectures             : 15
% 0.20/0.38  # Proof object clause conjectures      : 12
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 8
% 0.20/0.38  # Proof object initial formulas used   : 3
% 0.20/0.38  # Proof object generating inferences   : 7
% 0.20/0.38  # Proof object simplifying inferences  : 5
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 18
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 27
% 0.20/0.38  # Removed in clause preprocessing      : 2
% 0.20/0.38  # Initial clauses in saturation        : 25
% 0.20/0.38  # Processed clauses                    : 113
% 0.20/0.38  # ...of these trivial                  : 5
% 0.20/0.38  # ...subsumed                          : 30
% 0.20/0.38  # ...remaining for further processing  : 78
% 0.20/0.38  # Other redundant clauses eliminated   : 1
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 6
% 0.20/0.38  # Generated clauses                    : 123
% 0.20/0.38  # ...of the previous two non-trivial   : 89
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 122
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 1
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 47
% 0.20/0.38  #    Positive orientable unit clauses  : 20
% 0.20/0.38  #    Positive unorientable unit clauses: 1
% 0.20/0.38  #    Negative unit clauses             : 11
% 0.20/0.38  #    Non-unit-clauses                  : 15
% 0.20/0.38  # Current number of unprocessed clauses: 25
% 0.20/0.38  # ...number of literals in the above   : 43
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 33
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 35
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 31
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.20/0.38  # Unit Clause-clause subsumption calls : 29
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 7
% 0.20/0.38  # BW rewrite match successes           : 6
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 2645
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.032 s
% 0.20/0.38  # System time              : 0.002 s
% 0.20/0.38  # Total time               : 0.034 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
