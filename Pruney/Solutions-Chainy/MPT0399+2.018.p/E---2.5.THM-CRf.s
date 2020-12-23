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
% DateTime   : Thu Dec  3 10:47:26 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   23 (  51 expanded)
%              Number of clauses        :   12 (  23 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 ( 144 expanded)
%              Number of equality atoms :   22 (  55 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_setfam_1,conjecture,(
    ! [X1] :
      ( r1_setfam_1(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( r1_setfam_1(X1,k1_xboole_0)
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t21_setfam_1])).

fof(c_0_6,plain,(
    ! [X17,X18] :
      ( ( k4_xboole_0(X17,k1_tarski(X18)) != X17
        | ~ r2_hidden(X18,X17) )
      & ( r2_hidden(X18,X17)
        | k4_xboole_0(X17,k1_tarski(X18)) = X17 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_7,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_8,plain,(
    ! [X19,X20,X21,X23,X24,X26] :
      ( ( r2_hidden(esk4_3(X19,X20,X21),X20)
        | ~ r2_hidden(X21,X19)
        | ~ r1_setfam_1(X19,X20) )
      & ( r1_tarski(X21,esk4_3(X19,X20,X21))
        | ~ r2_hidden(X21,X19)
        | ~ r1_setfam_1(X19,X20) )
      & ( r2_hidden(esk5_2(X23,X24),X23)
        | r1_setfam_1(X23,X24) )
      & ( ~ r2_hidden(X26,X24)
        | ~ r1_tarski(esk5_2(X23,X24),X26)
        | r1_setfam_1(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

fof(c_0_9,negated_conjecture,
    ( r1_setfam_1(esk6_0,k1_xboole_0)
    & esk6_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X6,X7,X8,X10,X11,X12,X13,X15] :
      ( ( r2_hidden(X8,esk1_3(X6,X7,X8))
        | ~ r2_hidden(X8,X7)
        | X7 != k3_tarski(X6) )
      & ( r2_hidden(esk1_3(X6,X7,X8),X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_tarski(X6) )
      & ( ~ r2_hidden(X10,X11)
        | ~ r2_hidden(X11,X6)
        | r2_hidden(X10,X7)
        | X7 != k3_tarski(X6) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | ~ r2_hidden(esk2_2(X12,X13),X15)
        | ~ r2_hidden(X15,X12)
        | X13 = k3_tarski(X12) )
      & ( r2_hidden(esk2_2(X12,X13),esk3_2(X12,X13))
        | r2_hidden(esk2_2(X12,X13),X13)
        | X13 = k3_tarski(X12) )
      & ( r2_hidden(esk3_2(X12,X13),X12)
        | r2_hidden(esk2_2(X12,X13),X13)
        | X13 = k3_tarski(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r1_setfam_1(esk6_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk4_3(esk6_0,k1_xboole_0,X1),k1_xboole_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( X1 = k3_tarski(k1_xboole_0)
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( k3_tarski(k1_xboole_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_15])).

cnf(c_0_20,plain,
    ( X1 = esk6_0
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_21,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_20]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n022.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 20:07:40 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  # Version: 2.5pre002
% 0.16/0.31  # No SInE strategy applied
% 0.16/0.31  # Trying AutoSched0 for 299 seconds
% 0.16/0.36  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.16/0.36  # and selection function SelectNewComplexAHP.
% 0.16/0.36  #
% 0.16/0.36  # Preprocessing time       : 0.044 s
% 0.16/0.36  
% 0.16/0.36  # Proof found!
% 0.16/0.36  # SZS status Theorem
% 0.16/0.36  # SZS output start CNFRefutation
% 0.16/0.36  fof(t21_setfam_1, conjecture, ![X1]:(r1_setfam_1(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 0.16/0.36  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.16/0.36  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.16/0.36  fof(d2_setfam_1, axiom, ![X1, X2]:(r1_setfam_1(X1,X2)<=>![X3]:~((r2_hidden(X3,X1)&![X4]:~((r2_hidden(X4,X2)&r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 0.16/0.36  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.16/0.36  fof(c_0_5, negated_conjecture, ~(![X1]:(r1_setfam_1(X1,k1_xboole_0)=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t21_setfam_1])).
% 0.16/0.36  fof(c_0_6, plain, ![X17, X18]:((k4_xboole_0(X17,k1_tarski(X18))!=X17|~r2_hidden(X18,X17))&(r2_hidden(X18,X17)|k4_xboole_0(X17,k1_tarski(X18))=X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.16/0.36  fof(c_0_7, plain, ![X5]:k4_xboole_0(k1_xboole_0,X5)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.16/0.36  fof(c_0_8, plain, ![X19, X20, X21, X23, X24, X26]:(((r2_hidden(esk4_3(X19,X20,X21),X20)|~r2_hidden(X21,X19)|~r1_setfam_1(X19,X20))&(r1_tarski(X21,esk4_3(X19,X20,X21))|~r2_hidden(X21,X19)|~r1_setfam_1(X19,X20)))&((r2_hidden(esk5_2(X23,X24),X23)|r1_setfam_1(X23,X24))&(~r2_hidden(X26,X24)|~r1_tarski(esk5_2(X23,X24),X26)|r1_setfam_1(X23,X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).
% 0.16/0.36  fof(c_0_9, negated_conjecture, (r1_setfam_1(esk6_0,k1_xboole_0)&esk6_0!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.16/0.36  cnf(c_0_10, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.16/0.36  cnf(c_0_11, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.16/0.36  fof(c_0_12, plain, ![X6, X7, X8, X10, X11, X12, X13, X15]:((((r2_hidden(X8,esk1_3(X6,X7,X8))|~r2_hidden(X8,X7)|X7!=k3_tarski(X6))&(r2_hidden(esk1_3(X6,X7,X8),X6)|~r2_hidden(X8,X7)|X7!=k3_tarski(X6)))&(~r2_hidden(X10,X11)|~r2_hidden(X11,X6)|r2_hidden(X10,X7)|X7!=k3_tarski(X6)))&((~r2_hidden(esk2_2(X12,X13),X13)|(~r2_hidden(esk2_2(X12,X13),X15)|~r2_hidden(X15,X12))|X13=k3_tarski(X12))&((r2_hidden(esk2_2(X12,X13),esk3_2(X12,X13))|r2_hidden(esk2_2(X12,X13),X13)|X13=k3_tarski(X12))&(r2_hidden(esk3_2(X12,X13),X12)|r2_hidden(esk2_2(X12,X13),X13)|X13=k3_tarski(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.16/0.36  cnf(c_0_13, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|~r2_hidden(X3,X1)|~r1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.16/0.36  cnf(c_0_14, negated_conjecture, (r1_setfam_1(esk6_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.36  cnf(c_0_15, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.16/0.36  cnf(c_0_16, plain, (r2_hidden(esk3_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.16/0.36  cnf(c_0_17, negated_conjecture, (r2_hidden(esk4_3(esk6_0,k1_xboole_0,X1),k1_xboole_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.16/0.36  cnf(c_0_18, plain, (X1=k3_tarski(k1_xboole_0)|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.16/0.36  cnf(c_0_19, negated_conjecture, (k3_tarski(k1_xboole_0)=esk6_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_15])).
% 0.16/0.36  cnf(c_0_20, plain, (X1=esk6_0|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.16/0.36  cnf(c_0_21, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.36  cnf(c_0_22, plain, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_20]), c_0_21]), ['proof']).
% 0.16/0.36  # SZS output end CNFRefutation
% 0.16/0.36  # Proof object total steps             : 23
% 0.16/0.36  # Proof object clause steps            : 12
% 0.16/0.36  # Proof object formula steps           : 11
% 0.16/0.36  # Proof object conjectures             : 7
% 0.16/0.36  # Proof object clause conjectures      : 4
% 0.16/0.36  # Proof object formula conjectures     : 3
% 0.16/0.36  # Proof object initial clauses used    : 6
% 0.16/0.36  # Proof object initial formulas used   : 5
% 0.16/0.36  # Proof object generating inferences   : 5
% 0.16/0.36  # Proof object simplifying inferences  : 3
% 0.16/0.36  # Training examples: 0 positive, 0 negative
% 0.16/0.36  # Parsed axioms                        : 5
% 0.16/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.36  # Initial clauses                      : 15
% 0.16/0.36  # Removed in clause preprocessing      : 0
% 0.16/0.36  # Initial clauses in saturation        : 15
% 0.16/0.36  # Processed clauses                    : 32
% 0.16/0.36  # ...of these trivial                  : 0
% 0.16/0.36  # ...subsumed                          : 3
% 0.16/0.36  # ...remaining for further processing  : 29
% 0.16/0.36  # Other redundant clauses eliminated   : 0
% 0.16/0.36  # Clauses deleted for lack of memory   : 0
% 0.16/0.36  # Backward-subsumed                    : 0
% 0.16/0.36  # Backward-rewritten                   : 2
% 0.16/0.36  # Generated clauses                    : 55
% 0.16/0.36  # ...of the previous two non-trivial   : 50
% 0.16/0.36  # Contextual simplify-reflections      : 1
% 0.16/0.36  # Paramodulations                      : 51
% 0.16/0.36  # Factorizations                       : 0
% 0.16/0.36  # Equation resolutions                 : 4
% 0.16/0.36  # Propositional unsat checks           : 0
% 0.16/0.36  #    Propositional check models        : 0
% 0.16/0.36  #    Propositional check unsatisfiable : 0
% 0.16/0.36  #    Propositional clauses             : 0
% 0.16/0.36  #    Propositional clauses after purity: 0
% 0.16/0.36  #    Propositional unsat core size     : 0
% 0.16/0.36  #    Propositional preprocessing time  : 0.000
% 0.16/0.36  #    Propositional encoding time       : 0.000
% 0.16/0.36  #    Propositional solver time         : 0.000
% 0.16/0.36  #    Success case prop preproc time    : 0.000
% 0.16/0.36  #    Success case prop encoding time   : 0.000
% 0.16/0.36  #    Success case prop solver time     : 0.000
% 0.16/0.36  # Current number of processed clauses  : 27
% 0.16/0.36  #    Positive orientable unit clauses  : 4
% 0.16/0.36  #    Positive unorientable unit clauses: 0
% 0.16/0.36  #    Negative unit clauses             : 3
% 0.16/0.36  #    Non-unit-clauses                  : 20
% 0.16/0.36  # Current number of unprocessed clauses: 30
% 0.16/0.36  # ...number of literals in the above   : 86
% 0.16/0.36  # Current number of archived formulas  : 0
% 0.16/0.36  # Current number of archived clauses   : 2
% 0.16/0.36  # Clause-clause subsumption calls (NU) : 44
% 0.16/0.36  # Rec. Clause-clause subsumption calls : 31
% 0.16/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.16/0.36  # Unit Clause-clause subsumption calls : 30
% 0.16/0.36  # Rewrite failures with RHS unbound    : 0
% 0.16/0.36  # BW rewrite match attempts            : 2
% 0.16/0.36  # BW rewrite match successes           : 2
% 0.16/0.36  # Condensation attempts                : 0
% 0.16/0.36  # Condensation successes               : 0
% 0.16/0.36  # Termbank termtop insertions          : 1615
% 0.16/0.36  
% 0.16/0.36  # -------------------------------------------------
% 0.16/0.36  # User time                : 0.047 s
% 0.16/0.36  # System time              : 0.004 s
% 0.16/0.36  # Total time               : 0.051 s
% 0.16/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
