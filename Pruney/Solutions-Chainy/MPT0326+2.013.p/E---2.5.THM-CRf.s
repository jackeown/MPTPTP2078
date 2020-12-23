%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:14 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   26 (  51 expanded)
%              Number of clauses        :   16 (  20 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   66 ( 152 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t139_zfmisc_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2,X3,X4] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
            | r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)) )
         => r1_tarski(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(t138_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2,X3,X4] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
              | r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)) )
           => r1_tarski(X2,X4) ) ) ),
    inference(assume_negation,[status(cth)],[t139_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X9,X10,X11,X12] :
      ( ( r1_tarski(X9,X11)
        | k2_zfmisc_1(X9,X10) = k1_xboole_0
        | ~ r1_tarski(k2_zfmisc_1(X9,X10),k2_zfmisc_1(X11,X12)) )
      & ( r1_tarski(X10,X12)
        | k2_zfmisc_1(X9,X10) = k1_xboole_0
        | ~ r1_tarski(k2_zfmisc_1(X9,X10),k2_zfmisc_1(X11,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_zfmisc_1])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
      | r1_tarski(k2_zfmisc_1(esk2_0,esk1_0),k2_zfmisc_1(esk4_0,esk3_0)) )
    & ~ r1_tarski(esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,X2)
    | k2_zfmisc_1(X1,X3) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
    | r1_tarski(k2_zfmisc_1(esk2_0,esk1_0),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X6,X7,X8] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X7,X6),k2_zfmisc_1(X8,X6))
        | X6 = k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(k2_zfmisc_1(X6,X7),k2_zfmisc_1(X6,X8))
        | X6 = k1_xboole_0
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | k2_zfmisc_1(X3,X1) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk1_0) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])).

fof(c_0_14,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_15,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk1_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_10])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_19,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_17])])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_21])).

cnf(c_0_24,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03DI
% 0.13/0.39  # and selection function PSelectComplexExceptRRHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.048 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t139_zfmisc_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2, X3, X4]:((r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)))=>r1_tarski(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 0.13/0.39  fof(t138_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.13/0.39  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.13/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.39  fof(c_0_5, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2, X3, X4]:((r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)))=>r1_tarski(X2,X4)))), inference(assume_negation,[status(cth)],[t139_zfmisc_1])).
% 0.13/0.39  fof(c_0_6, plain, ![X9, X10, X11, X12]:((r1_tarski(X9,X11)|k2_zfmisc_1(X9,X10)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X9,X10),k2_zfmisc_1(X11,X12)))&(r1_tarski(X10,X12)|k2_zfmisc_1(X9,X10)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X9,X10),k2_zfmisc_1(X11,X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_zfmisc_1])])])).
% 0.13/0.39  fof(c_0_7, negated_conjecture, (~v1_xboole_0(esk1_0)&((r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))|r1_tarski(k2_zfmisc_1(esk2_0,esk1_0),k2_zfmisc_1(esk4_0,esk3_0)))&~r1_tarski(esk2_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.13/0.39  cnf(c_0_8, plain, (r1_tarski(X1,X2)|k2_zfmisc_1(X1,X3)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_9, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))|r1_tarski(k2_zfmisc_1(esk2_0,esk1_0),k2_zfmisc_1(esk4_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_10, negated_conjecture, (~r1_tarski(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  fof(c_0_11, plain, ![X6, X7, X8]:((~r1_tarski(k2_zfmisc_1(X7,X6),k2_zfmisc_1(X8,X6))|X6=k1_xboole_0|r1_tarski(X7,X8))&(~r1_tarski(k2_zfmisc_1(X6,X7),k2_zfmisc_1(X6,X8))|X6=k1_xboole_0|r1_tarski(X7,X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.13/0.39  cnf(c_0_12, plain, (r1_tarski(X1,X2)|k2_zfmisc_1(X3,X1)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.39  cnf(c_0_13, negated_conjecture, (k2_zfmisc_1(esk2_0,esk1_0)=k1_xboole_0|r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10])).
% 0.13/0.39  fof(c_0_14, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.39  cnf(c_0_15, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_16, negated_conjecture, (k2_zfmisc_1(esk2_0,esk1_0)=k1_xboole_0|k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_10])).
% 0.13/0.39  cnf(c_0_17, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_18, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|esk1_0=k1_xboole_0|r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.13/0.39  cnf(c_0_19, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_20, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_10, c_0_18])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (esk1_0=k1_xboole_0|r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_17])])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_10, c_0_21])).
% 0.13/0.39  cnf(c_0_24, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 26
% 0.13/0.39  # Proof object clause steps            : 16
% 0.13/0.39  # Proof object formula steps           : 10
% 0.13/0.39  # Proof object conjectures             : 13
% 0.13/0.39  # Proof object clause conjectures      : 10
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 9
% 0.13/0.39  # Proof object initial formulas used   : 5
% 0.13/0.39  # Proof object generating inferences   : 6
% 0.13/0.39  # Proof object simplifying inferences  : 9
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 5
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 9
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 9
% 0.13/0.39  # Processed clauses                    : 29
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 2
% 0.13/0.39  # ...remaining for further processing  : 27
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 3
% 0.13/0.39  # Backward-rewritten                   : 7
% 0.13/0.39  # Generated clauses                    : 22
% 0.13/0.39  # ...of the previous two non-trivial   : 23
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 22
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 8
% 0.13/0.39  #    Positive orientable unit clauses  : 3
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 1
% 0.13/0.39  #    Non-unit-clauses                  : 4
% 0.13/0.39  # Current number of unprocessed clauses: 8
% 0.13/0.39  # ...number of literals in the above   : 30
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 19
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 31
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 26
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 5
% 0.13/0.39  # Unit Clause-clause subsumption calls : 0
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 1
% 0.13/0.39  # BW rewrite match successes           : 1
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 940
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.052 s
% 0.13/0.39  # System time              : 0.003 s
% 0.13/0.39  # Total time               : 0.055 s
% 0.13/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
