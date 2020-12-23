%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:56 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   19 (  62 expanded)
%              Number of clauses        :   10 (  27 expanded)
%              Number of leaves         :    4 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 252 expanded)
%              Number of equality atoms :   18 (  68 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(t2_zfmisc_1,conjecture,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(c_0_4,plain,(
    ! [X5,X6,X7] :
      ( ( ~ r2_hidden(X5,X6)
        | ~ r2_hidden(X5,X7)
        | ~ r2_hidden(X5,k5_xboole_0(X6,X7)) )
      & ( r2_hidden(X5,X6)
        | r2_hidden(X5,X7)
        | ~ r2_hidden(X5,k5_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X5,X6)
        | r2_hidden(X5,X7)
        | r2_hidden(X5,k5_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X5,X7)
        | r2_hidden(X5,X6)
        | r2_hidden(X5,k5_xboole_0(X6,X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

fof(c_0_5,plain,(
    ! [X8] : k5_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_6,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X13,X14,X15,X16,X18] :
      ( ( r2_hidden(X11,esk1_3(X9,X10,X11))
        | ~ r2_hidden(X11,X10)
        | X10 != k3_tarski(X9) )
      & ( r2_hidden(esk1_3(X9,X10,X11),X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_tarski(X9) )
      & ( ~ r2_hidden(X13,X14)
        | ~ r2_hidden(X14,X9)
        | r2_hidden(X13,X10)
        | X10 != k3_tarski(X9) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | ~ r2_hidden(esk2_2(X15,X16),X18)
        | ~ r2_hidden(X18,X15)
        | X16 = k3_tarski(X15) )
      & ( r2_hidden(esk2_2(X15,X16),esk3_2(X15,X16))
        | r2_hidden(esk2_2(X15,X16),X16)
        | X16 = k3_tarski(X15) )
      & ( r2_hidden(esk3_2(X15,X16),X15)
        | r2_hidden(esk2_2(X15,X16),X16)
        | X16 = k3_tarski(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t2_zfmisc_1])).

cnf(c_0_12,plain,
    ( X1 = k3_tarski(k1_xboole_0)
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1)
    | ~ r2_hidden(esk3_2(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_13,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( X1 = k3_tarski(k1_xboole_0)
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(esk2_2(k1_xboole_0,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_14]),c_0_15])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_2(X1,X2),esk3_2(X1,X2))
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_15]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:19:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.13/0.37  # and selection function SelectNewComplexAHP.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.13/0.37  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.13/0.37  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.13/0.37  fof(t2_zfmisc_1, conjecture, k3_tarski(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 0.13/0.37  fof(c_0_4, plain, ![X5, X6, X7]:(((~r2_hidden(X5,X6)|~r2_hidden(X5,X7)|~r2_hidden(X5,k5_xboole_0(X6,X7)))&(r2_hidden(X5,X6)|r2_hidden(X5,X7)|~r2_hidden(X5,k5_xboole_0(X6,X7))))&((~r2_hidden(X5,X6)|r2_hidden(X5,X7)|r2_hidden(X5,k5_xboole_0(X6,X7)))&(~r2_hidden(X5,X7)|r2_hidden(X5,X6)|r2_hidden(X5,k5_xboole_0(X6,X7))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.13/0.37  fof(c_0_5, plain, ![X8]:k5_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.13/0.37  cnf(c_0_6, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  cnf(c_0_7, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  fof(c_0_8, plain, ![X9, X10, X11, X13, X14, X15, X16, X18]:((((r2_hidden(X11,esk1_3(X9,X10,X11))|~r2_hidden(X11,X10)|X10!=k3_tarski(X9))&(r2_hidden(esk1_3(X9,X10,X11),X9)|~r2_hidden(X11,X10)|X10!=k3_tarski(X9)))&(~r2_hidden(X13,X14)|~r2_hidden(X14,X9)|r2_hidden(X13,X10)|X10!=k3_tarski(X9)))&((~r2_hidden(esk2_2(X15,X16),X16)|(~r2_hidden(esk2_2(X15,X16),X18)|~r2_hidden(X18,X15))|X16=k3_tarski(X15))&((r2_hidden(esk2_2(X15,X16),esk3_2(X15,X16))|r2_hidden(esk2_2(X15,X16),X16)|X16=k3_tarski(X15))&(r2_hidden(esk3_2(X15,X16),X15)|r2_hidden(esk2_2(X15,X16),X16)|X16=k3_tarski(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.13/0.37  cnf(c_0_9, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.13/0.37  cnf(c_0_10, plain, (r2_hidden(esk3_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  fof(c_0_11, negated_conjecture, ~(k3_tarski(k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t2_zfmisc_1])).
% 0.13/0.37  cnf(c_0_12, plain, (X1=k3_tarski(k1_xboole_0)|r2_hidden(esk2_2(k1_xboole_0,X1),X1)|~r2_hidden(esk3_2(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.37  fof(c_0_13, negated_conjecture, k3_tarski(k1_xboole_0)!=k1_xboole_0, inference(fof_simplification,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_14, plain, (X1=k3_tarski(k1_xboole_0)|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_12, c_0_10])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_16, plain, (~r2_hidden(esk2_2(k1_xboole_0,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_14]), c_0_15])).
% 0.13/0.37  cnf(c_0_17, plain, (r2_hidden(esk2_2(X1,X2),esk3_2(X1,X2))|r2_hidden(esk2_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_18, plain, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_15]), c_0_16]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 19
% 0.13/0.37  # Proof object clause steps            : 10
% 0.13/0.37  # Proof object formula steps           : 9
% 0.13/0.37  # Proof object conjectures             : 4
% 0.13/0.37  # Proof object clause conjectures      : 1
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 5
% 0.13/0.37  # Proof object initial formulas used   : 4
% 0.13/0.37  # Proof object generating inferences   : 5
% 0.13/0.37  # Proof object simplifying inferences  : 3
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 4
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 12
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 12
% 0.13/0.37  # Processed clauses                    : 25
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 25
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 1
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 74
% 0.13/0.37  # ...of the previous two non-trivial   : 66
% 0.13/0.37  # Contextual simplify-reflections      : 1
% 0.13/0.37  # Paramodulations                      : 69
% 0.13/0.37  # Factorizations                       : 2
% 0.13/0.37  # Equation resolutions                 : 3
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
% 0.13/0.37  # Current number of processed clauses  : 24
% 0.13/0.37  #    Positive orientable unit clauses  : 1
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 21
% 0.13/0.37  # Current number of unprocessed clauses: 53
% 0.13/0.37  # ...number of literals in the above   : 202
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 1
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 46
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 26
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1870
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.029 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.032 s
% 0.13/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
