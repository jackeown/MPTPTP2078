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
% DateTime   : Thu Dec  3 10:47:04 EST 2020

% Result     : Theorem 0.09s
% Output     : CNFRefutation 0.09s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 (  76 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t5_setfam_1,conjecture,(
    ! [X1] :
      ( r2_hidden(k1_xboole_0,X1)
     => k1_setfam_1(X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_7,plain,(
    ! [X13,X14] :
      ( ( k2_zfmisc_1(X13,X14) != k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_8,plain,(
    ! [X15,X16] : ~ r2_hidden(X15,k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_9,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( v1_xboole_0(X12)
      | ~ r1_tarski(X12,X11)
      | ~ r1_xboole_0(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_11,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | r1_tarski(k1_setfam_1(X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r2_hidden(esk1_2(X5,X6),X5)
        | r1_xboole_0(X5,X6) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | r1_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_15,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( r2_hidden(k1_xboole_0,X1)
       => k1_setfam_1(X1) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t5_setfam_1])).

fof(c_0_20,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_21,plain,
    ( v1_xboole_0(k1_setfam_1(X1))
    | ~ r2_hidden(X2,X1)
    | ~ r1_xboole_0(k1_setfam_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk2_0)
    & k1_setfam_1(esk2_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( v1_xboole_0(k1_setfam_1(X1))
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k1_setfam_1(esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k1_setfam_1(X1) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.08  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.09/0.27  % Computer   : n019.cluster.edu
% 0.09/0.27  % Model      : x86_64 x86_64
% 0.09/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.27  % Memory     : 8042.1875MB
% 0.09/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.27  % CPULimit   : 60
% 0.09/0.27  % WCLimit    : 600
% 0.09/0.27  % DateTime   : Tue Dec  1 11:46:07 EST 2020
% 0.09/0.27  % CPUTime    : 
% 0.09/0.27  # Version: 2.5pre002
% 0.09/0.27  # No SInE strategy applied
% 0.09/0.27  # Trying AutoSched0 for 299 seconds
% 0.09/0.29  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.09/0.29  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.09/0.29  #
% 0.09/0.29  # Preprocessing time       : 0.016 s
% 0.09/0.29  
% 0.09/0.29  # Proof found!
% 0.09/0.29  # SZS status Theorem
% 0.09/0.29  # SZS output start CNFRefutation
% 0.09/0.29  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.09/0.29  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.09/0.29  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.09/0.29  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.09/0.29  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.09/0.29  fof(t5_setfam_1, conjecture, ![X1]:(r2_hidden(k1_xboole_0,X1)=>k1_setfam_1(X1)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_setfam_1)).
% 0.09/0.29  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.09/0.29  fof(c_0_7, plain, ![X13, X14]:((k2_zfmisc_1(X13,X14)!=k1_xboole_0|(X13=k1_xboole_0|X14=k1_xboole_0))&((X13!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0)&(X14!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.09/0.29  fof(c_0_8, plain, ![X15, X16]:~r2_hidden(X15,k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.09/0.29  cnf(c_0_9, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.09/0.29  fof(c_0_10, plain, ![X11, X12]:(v1_xboole_0(X12)|(~r1_tarski(X12,X11)|~r1_xboole_0(X12,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.09/0.29  fof(c_0_11, plain, ![X17, X18]:(~r2_hidden(X17,X18)|r1_tarski(k1_setfam_1(X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.09/0.29  cnf(c_0_12, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.09/0.29  cnf(c_0_13, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_9])).
% 0.09/0.29  fof(c_0_14, plain, ![X5, X6, X8, X9, X10]:(((r2_hidden(esk1_2(X5,X6),X5)|r1_xboole_0(X5,X6))&(r2_hidden(esk1_2(X5,X6),X6)|r1_xboole_0(X5,X6)))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|~r1_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.09/0.29  cnf(c_0_15, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.09/0.29  cnf(c_0_16, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.09/0.29  cnf(c_0_17, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.09/0.29  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.09/0.29  fof(c_0_19, negated_conjecture, ~(![X1]:(r2_hidden(k1_xboole_0,X1)=>k1_setfam_1(X1)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t5_setfam_1])).
% 0.09/0.29  fof(c_0_20, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.09/0.29  cnf(c_0_21, plain, (v1_xboole_0(k1_setfam_1(X1))|~r2_hidden(X2,X1)|~r1_xboole_0(k1_setfam_1(X1),X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.09/0.29  cnf(c_0_22, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.09/0.29  fof(c_0_23, negated_conjecture, (r2_hidden(k1_xboole_0,esk2_0)&k1_setfam_1(esk2_0)!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.09/0.29  cnf(c_0_24, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.09/0.29  cnf(c_0_25, plain, (v1_xboole_0(k1_setfam_1(X1))|~r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.09/0.29  cnf(c_0_26, negated_conjecture, (k1_setfam_1(esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.09/0.29  cnf(c_0_27, plain, (k1_setfam_1(X1)=k1_xboole_0|~r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.09/0.29  cnf(c_0_28, negated_conjecture, (r2_hidden(k1_xboole_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.09/0.29  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])]), ['proof']).
% 0.09/0.29  # SZS output end CNFRefutation
% 0.09/0.29  # Proof object total steps             : 30
% 0.09/0.29  # Proof object clause steps            : 15
% 0.09/0.29  # Proof object formula steps           : 15
% 0.09/0.29  # Proof object conjectures             : 6
% 0.09/0.29  # Proof object clause conjectures      : 3
% 0.09/0.29  # Proof object formula conjectures     : 3
% 0.09/0.29  # Proof object initial clauses used    : 8
% 0.09/0.29  # Proof object initial formulas used   : 7
% 0.09/0.29  # Proof object generating inferences   : 6
% 0.09/0.29  # Proof object simplifying inferences  : 3
% 0.09/0.29  # Training examples: 0 positive, 0 negative
% 0.09/0.29  # Parsed axioms                        : 7
% 0.09/0.29  # Removed by relevancy pruning/SinE    : 0
% 0.09/0.29  # Initial clauses                      : 12
% 0.09/0.29  # Removed in clause preprocessing      : 0
% 0.09/0.29  # Initial clauses in saturation        : 12
% 0.09/0.29  # Processed clauses                    : 23
% 0.09/0.29  # ...of these trivial                  : 0
% 0.09/0.29  # ...subsumed                          : 2
% 0.09/0.29  # ...remaining for further processing  : 21
% 0.09/0.29  # Other redundant clauses eliminated   : 2
% 0.09/0.29  # Clauses deleted for lack of memory   : 0
% 0.09/0.29  # Backward-subsumed                    : 0
% 0.09/0.29  # Backward-rewritten                   : 0
% 0.09/0.29  # Generated clauses                    : 17
% 0.09/0.29  # ...of the previous two non-trivial   : 13
% 0.09/0.29  # Contextual simplify-reflections      : 0
% 0.09/0.29  # Paramodulations                      : 15
% 0.09/0.29  # Factorizations                       : 0
% 0.09/0.29  # Equation resolutions                 : 2
% 0.09/0.29  # Propositional unsat checks           : 0
% 0.09/0.29  #    Propositional check models        : 0
% 0.09/0.29  #    Propositional check unsatisfiable : 0
% 0.09/0.29  #    Propositional clauses             : 0
% 0.09/0.29  #    Propositional clauses after purity: 0
% 0.09/0.29  #    Propositional unsat core size     : 0
% 0.09/0.29  #    Propositional preprocessing time  : 0.000
% 0.09/0.29  #    Propositional encoding time       : 0.000
% 0.09/0.29  #    Propositional solver time         : 0.000
% 0.09/0.29  #    Success case prop preproc time    : 0.000
% 0.09/0.29  #    Success case prop encoding time   : 0.000
% 0.09/0.29  #    Success case prop solver time     : 0.000
% 0.09/0.29  # Current number of processed clauses  : 19
% 0.09/0.29  #    Positive orientable unit clauses  : 5
% 0.09/0.29  #    Positive unorientable unit clauses: 0
% 0.09/0.29  #    Negative unit clauses             : 3
% 0.09/0.29  #    Non-unit-clauses                  : 11
% 0.09/0.29  # Current number of unprocessed clauses: 2
% 0.09/0.29  # ...number of literals in the above   : 6
% 0.09/0.29  # Current number of archived formulas  : 0
% 0.09/0.29  # Current number of archived clauses   : 0
% 0.09/0.29  # Clause-clause subsumption calls (NU) : 7
% 0.09/0.29  # Rec. Clause-clause subsumption calls : 5
% 0.09/0.29  # Non-unit clause-clause subsumptions  : 0
% 0.09/0.29  # Unit Clause-clause subsumption calls : 4
% 0.09/0.29  # Rewrite failures with RHS unbound    : 0
% 0.09/0.29  # BW rewrite match attempts            : 0
% 0.09/0.29  # BW rewrite match successes           : 0
% 0.09/0.29  # Condensation attempts                : 0
% 0.09/0.29  # Condensation successes               : 0
% 0.09/0.29  # Termbank termtop insertions          : 844
% 0.09/0.29  
% 0.09/0.29  # -------------------------------------------------
% 0.09/0.29  # User time                : 0.017 s
% 0.09/0.29  # System time              : 0.002 s
% 0.09/0.29  # Total time               : 0.018 s
% 0.09/0.29  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
