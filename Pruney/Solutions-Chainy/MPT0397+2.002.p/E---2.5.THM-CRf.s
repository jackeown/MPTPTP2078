%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:23 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   23 (  41 expanded)
%              Number of clauses        :   14 (  16 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 ( 136 expanded)
%              Number of equality atoms :   10 (  26 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(d3_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X2)
            & ! [X4] :
                ~ ( r2_hidden(X4,X1)
                  & r1_tarski(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_setfam_1)).

fof(t19_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r2_setfam_1(X2,X1)
     => ( X1 = k1_xboole_0
        | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_setfam_1)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(c_0_4,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ r1_tarski(X16,X18)
      | r1_tarski(k1_setfam_1(X17),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X9,X10,X12] :
      ( ( r2_hidden(esk1_3(X5,X6,X7),X5)
        | ~ r2_hidden(X7,X6)
        | ~ r2_setfam_1(X5,X6) )
      & ( r1_tarski(esk1_3(X5,X6,X7),X7)
        | ~ r2_hidden(X7,X6)
        | ~ r2_setfam_1(X5,X6) )
      & ( r2_hidden(esk2_2(X9,X10),X10)
        | r2_setfam_1(X9,X10) )
      & ( ~ r2_hidden(X12,X9)
        | ~ r1_tarski(X12,esk2_2(X9,X10))
        | r2_setfam_1(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_setfam_1])])])])])])).

cnf(c_0_6,plain,
    ( r1_tarski(k1_setfam_1(X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | ~ r2_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_setfam_1(X2,X1)
       => ( X1 = k1_xboole_0
          | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t19_setfam_1])).

fof(c_0_9,plain,(
    ! [X13,X14] :
      ( ( r2_hidden(esk3_2(X13,X14),X13)
        | X13 = k1_xboole_0
        | r1_tarski(X14,k1_setfam_1(X13)) )
      & ( ~ r1_tarski(X14,esk3_2(X13,X14))
        | X13 = k1_xboole_0
        | r1_tarski(X14,k1_setfam_1(X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

cnf(c_0_10,plain,
    ( r1_tarski(k1_setfam_1(X1),X2)
    | ~ r1_tarski(esk1_3(X1,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ r2_setfam_1(X1,X3) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_11,plain,
    ( r1_tarski(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(X3,X2)
    | ~ r2_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_12,negated_conjecture,
    ( r2_setfam_1(esk5_0,esk4_0)
    & esk4_0 != k1_xboole_0
    & ~ r1_tarski(k1_setfam_1(esk5_0),k1_setfam_1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk3_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_setfam_1(X1,X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk5_0),k1_setfam_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))
    | ~ r2_hidden(esk3_2(X1,k1_setfam_1(X2)),X3)
    | ~ r2_setfam_1(X2,X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(esk3_2(esk4_0,k1_setfam_1(esk5_0)),X1)
    | ~ r2_setfam_1(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( r2_setfam_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,k1_setfam_1(esk5_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_18]),c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:40:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.14/0.38  # and selection function SelectVGNonCR.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.026 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t8_setfam_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_setfam_1)).
% 0.14/0.38  fof(d3_setfam_1, axiom, ![X1, X2]:(r2_setfam_1(X1,X2)<=>![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X1)&r1_tarski(X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_setfam_1)).
% 0.14/0.38  fof(t19_setfam_1, conjecture, ![X1, X2]:(r2_setfam_1(X2,X1)=>(X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_setfam_1)).
% 0.14/0.38  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 0.14/0.38  fof(c_0_4, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~r1_tarski(X16,X18)|r1_tarski(k1_setfam_1(X17),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).
% 0.14/0.38  fof(c_0_5, plain, ![X5, X6, X7, X9, X10, X12]:(((r2_hidden(esk1_3(X5,X6,X7),X5)|~r2_hidden(X7,X6)|~r2_setfam_1(X5,X6))&(r1_tarski(esk1_3(X5,X6,X7),X7)|~r2_hidden(X7,X6)|~r2_setfam_1(X5,X6)))&((r2_hidden(esk2_2(X9,X10),X10)|r2_setfam_1(X9,X10))&(~r2_hidden(X12,X9)|~r1_tarski(X12,esk2_2(X9,X10))|r2_setfam_1(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_setfam_1])])])])])])).
% 0.14/0.38  cnf(c_0_6, plain, (r1_tarski(k1_setfam_1(X2),X3)|~r2_hidden(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.38  cnf(c_0_7, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|~r2_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(r2_setfam_1(X2,X1)=>(X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))))), inference(assume_negation,[status(cth)],[t19_setfam_1])).
% 0.14/0.38  fof(c_0_9, plain, ![X13, X14]:((r2_hidden(esk3_2(X13,X14),X13)|(X13=k1_xboole_0|r1_tarski(X14,k1_setfam_1(X13))))&(~r1_tarski(X14,esk3_2(X13,X14))|(X13=k1_xboole_0|r1_tarski(X14,k1_setfam_1(X13))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 0.14/0.38  cnf(c_0_10, plain, (r1_tarski(k1_setfam_1(X1),X2)|~r1_tarski(esk1_3(X1,X3,X4),X2)|~r2_hidden(X4,X3)|~r2_setfam_1(X1,X3)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.14/0.38  cnf(c_0_11, plain, (r1_tarski(esk1_3(X1,X2,X3),X3)|~r2_hidden(X3,X2)|~r2_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  fof(c_0_12, negated_conjecture, (r2_setfam_1(esk5_0,esk4_0)&(esk4_0!=k1_xboole_0&~r1_tarski(k1_setfam_1(esk5_0),k1_setfam_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.14/0.38  cnf(c_0_13, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk3_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_14, plain, (r1_tarski(k1_setfam_1(X1),X2)|~r2_hidden(X2,X3)|~r2_setfam_1(X1,X3)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (~r1_tarski(k1_setfam_1(esk5_0),k1_setfam_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_16, plain, (X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))|~r2_hidden(esk3_2(X1,k1_setfam_1(X2)),X3)|~r2_setfam_1(X2,X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_18, plain, (r2_hidden(esk3_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (~r2_hidden(esk3_2(esk4_0,k1_setfam_1(esk5_0)),X1)|~r2_setfam_1(esk5_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (r2_setfam_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (r2_hidden(esk3_2(esk4_0,k1_setfam_1(esk5_0)),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_18]), c_0_17])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 23
% 0.14/0.38  # Proof object clause steps            : 14
% 0.14/0.38  # Proof object formula steps           : 9
% 0.14/0.38  # Proof object conjectures             : 9
% 0.14/0.38  # Proof object clause conjectures      : 6
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 8
% 0.14/0.38  # Proof object initial formulas used   : 4
% 0.14/0.38  # Proof object generating inferences   : 6
% 0.14/0.38  # Proof object simplifying inferences  : 4
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 4
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 10
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 10
% 0.14/0.38  # Processed clauses                    : 31
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 31
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 16
% 0.14/0.38  # ...of the previous two non-trivial   : 15
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 16
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 21
% 0.14/0.38  #    Positive orientable unit clauses  : 2
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 3
% 0.14/0.38  #    Non-unit-clauses                  : 16
% 0.14/0.38  # Current number of unprocessed clauses: 4
% 0.14/0.38  # ...number of literals in the above   : 16
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 10
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 17
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 14
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.38  # Unit Clause-clause subsumption calls : 0
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 0
% 0.14/0.38  # BW rewrite match successes           : 0
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1002
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.029 s
% 0.14/0.38  # System time              : 0.002 s
% 0.14/0.38  # Total time               : 0.031 s
% 0.14/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
