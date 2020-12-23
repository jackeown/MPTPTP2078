%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:55 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   20 (  33 expanded)
%              Number of clauses        :   13 (  14 expanded)
%              Number of leaves         :    3 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 ( 111 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t110_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X2) )
       => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t110_xboole_1])).

fof(c_0_4,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_5,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    & r1_tarski(esk4_0,esk3_0)
    & ~ r1_tarski(k5_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X10,X11,X12] :
      ( ( ~ r2_hidden(X10,X11)
        | ~ r2_hidden(X10,X12)
        | ~ r2_hidden(X10,k5_xboole_0(X11,X12)) )
      & ( r2_hidden(X10,X11)
        | r2_hidden(X10,X12)
        | ~ r2_hidden(X10,k5_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X10,X11)
        | r2_hidden(X10,X12)
        | r2_hidden(X10,k5_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X10,X12)
        | r2_hidden(X10,X11)
        | r2_hidden(X10,k5_xboole_0(X11,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(k5_xboole_0(X1,X2),X3),X1)
    | r2_hidden(esk1_2(k5_xboole_0(X1,X2),X3),X2)
    | r1_tarski(k5_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),X2),esk3_0)
    | r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),X2),X1)
    | r1_tarski(k5_xboole_0(X1,esk4_0),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk1_2(k5_xboole_0(esk2_0,esk4_0),X1),esk3_0)
    | r1_tarski(k5_xboole_0(esk2_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:16:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.43  # AutoSched0-Mode selected heuristic G_E___092_C01_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.21/0.43  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.43  #
% 0.21/0.43  # Preprocessing time       : 0.027 s
% 0.21/0.43  # Presaturation interreduction done
% 0.21/0.43  
% 0.21/0.43  # Proof found!
% 0.21/0.43  # SZS status Theorem
% 0.21/0.43  # SZS output start CNFRefutation
% 0.21/0.43  fof(t110_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k5_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 0.21/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.43  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.21/0.43  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k5_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t110_xboole_1])).
% 0.21/0.43  fof(c_0_4, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.43  fof(c_0_5, negated_conjecture, ((r1_tarski(esk2_0,esk3_0)&r1_tarski(esk4_0,esk3_0))&~r1_tarski(k5_xboole_0(esk2_0,esk4_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.21/0.43  fof(c_0_6, plain, ![X10, X11, X12]:(((~r2_hidden(X10,X11)|~r2_hidden(X10,X12)|~r2_hidden(X10,k5_xboole_0(X11,X12)))&(r2_hidden(X10,X11)|r2_hidden(X10,X12)|~r2_hidden(X10,k5_xboole_0(X11,X12))))&((~r2_hidden(X10,X11)|r2_hidden(X10,X12)|r2_hidden(X10,k5_xboole_0(X11,X12)))&(~r2_hidden(X10,X12)|r2_hidden(X10,X11)|r2_hidden(X10,k5_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.21/0.43  cnf(c_0_7, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.21/0.43  cnf(c_0_8, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.43  cnf(c_0_9, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.43  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.21/0.43  cnf(c_0_11, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.43  cnf(c_0_12, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.21/0.43  cnf(c_0_13, plain, (r2_hidden(esk1_2(k5_xboole_0(X1,X2),X3),X1)|r2_hidden(esk1_2(k5_xboole_0(X1,X2),X3),X2)|r1_tarski(k5_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.21/0.43  cnf(c_0_14, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_7, c_0_11])).
% 0.21/0.43  cnf(c_0_15, negated_conjecture, (r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),X2),esk3_0)|r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),X2),X1)|r1_tarski(k5_xboole_0(X1,esk4_0),X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.21/0.43  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.21/0.43  cnf(c_0_17, negated_conjecture, (r2_hidden(esk1_2(k5_xboole_0(esk2_0,esk4_0),X1),esk3_0)|r1_tarski(k5_xboole_0(esk2_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.21/0.43  cnf(c_0_18, negated_conjecture, (~r1_tarski(k5_xboole_0(esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.43  cnf(c_0_19, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), ['proof']).
% 0.21/0.43  # SZS output end CNFRefutation
% 0.21/0.43  # Proof object total steps             : 20
% 0.21/0.43  # Proof object clause steps            : 13
% 0.21/0.43  # Proof object formula steps           : 7
% 0.21/0.43  # Proof object conjectures             : 11
% 0.21/0.43  # Proof object clause conjectures      : 8
% 0.21/0.43  # Proof object formula conjectures     : 3
% 0.21/0.43  # Proof object initial clauses used    : 7
% 0.21/0.43  # Proof object initial formulas used   : 3
% 0.21/0.43  # Proof object generating inferences   : 6
% 0.21/0.43  # Proof object simplifying inferences  : 1
% 0.21/0.43  # Training examples: 0 positive, 0 negative
% 0.21/0.43  # Parsed axioms                        : 3
% 0.21/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.43  # Initial clauses                      : 10
% 0.21/0.43  # Removed in clause preprocessing      : 0
% 0.21/0.43  # Initial clauses in saturation        : 10
% 0.21/0.43  # Processed clauses                    : 321
% 0.21/0.43  # ...of these trivial                  : 9
% 0.21/0.43  # ...subsumed                          : 102
% 0.21/0.43  # ...remaining for further processing  : 210
% 0.21/0.43  # Other redundant clauses eliminated   : 0
% 0.21/0.43  # Clauses deleted for lack of memory   : 0
% 0.21/0.43  # Backward-subsumed                    : 13
% 0.21/0.43  # Backward-rewritten                   : 15
% 0.21/0.43  # Generated clauses                    : 2321
% 0.21/0.43  # ...of the previous two non-trivial   : 2203
% 0.21/0.43  # Contextual simplify-reflections      : 9
% 0.21/0.43  # Paramodulations                      : 2303
% 0.21/0.43  # Factorizations                       : 18
% 0.21/0.43  # Equation resolutions                 : 0
% 0.21/0.43  # Propositional unsat checks           : 0
% 0.21/0.43  #    Propositional check models        : 0
% 0.21/0.43  #    Propositional check unsatisfiable : 0
% 0.21/0.43  #    Propositional clauses             : 0
% 0.21/0.43  #    Propositional clauses after purity: 0
% 0.21/0.43  #    Propositional unsat core size     : 0
% 0.21/0.43  #    Propositional preprocessing time  : 0.000
% 0.21/0.43  #    Propositional encoding time       : 0.000
% 0.21/0.43  #    Propositional solver time         : 0.000
% 0.21/0.43  #    Success case prop preproc time    : 0.000
% 0.21/0.43  #    Success case prop encoding time   : 0.000
% 0.21/0.43  #    Success case prop solver time     : 0.000
% 0.21/0.43  # Current number of processed clauses  : 172
% 0.21/0.43  #    Positive orientable unit clauses  : 50
% 0.21/0.43  #    Positive unorientable unit clauses: 0
% 0.21/0.43  #    Negative unit clauses             : 2
% 0.21/0.43  #    Non-unit-clauses                  : 120
% 0.21/0.43  # Current number of unprocessed clauses: 1883
% 0.21/0.43  # ...number of literals in the above   : 6711
% 0.21/0.43  # Current number of archived formulas  : 0
% 0.21/0.43  # Current number of archived clauses   : 38
% 0.21/0.43  # Clause-clause subsumption calls (NU) : 3448
% 0.21/0.43  # Rec. Clause-clause subsumption calls : 1849
% 0.21/0.43  # Non-unit clause-clause subsumptions  : 114
% 0.21/0.43  # Unit Clause-clause subsumption calls : 271
% 0.21/0.43  # Rewrite failures with RHS unbound    : 0
% 0.21/0.43  # BW rewrite match attempts            : 191
% 0.21/0.43  # BW rewrite match successes           : 14
% 0.21/0.43  # Condensation attempts                : 0
% 0.21/0.43  # Condensation successes               : 0
% 0.21/0.43  # Termbank termtop insertions          : 76064
% 0.21/0.44  
% 0.21/0.44  # -------------------------------------------------
% 0.21/0.44  # User time                : 0.081 s
% 0.21/0.44  # System time              : 0.009 s
% 0.21/0.44  # Total time               : 0.090 s
% 0.21/0.44  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
