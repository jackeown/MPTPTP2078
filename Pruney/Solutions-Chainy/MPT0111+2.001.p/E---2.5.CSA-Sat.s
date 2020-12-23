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
% DateTime   : Thu Dec  3 10:34:32 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 147 expanded)
%              Number of clauses        :   32 (  65 expanded)
%              Number of leaves         :    7 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :  102 ( 332 expanded)
%              Number of equality atoms :   45 ( 156 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t104_xboole_1,conjecture,(
    ! [X1,X2] :
      ( ~ ( ~ r2_xboole_0(X1,X2)
          & X1 != X2
          & ~ r2_xboole_0(X2,X1) )
    <=> r3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_xboole_1)).

fof(c_0_7,plain,(
    ! [X7,X8] :
      ( ( k4_xboole_0(X7,X8) != k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | k4_xboole_0(X7,X8) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_8,plain,(
    ! [X11,X12] : k4_xboole_0(k2_xboole_0(X11,X12),X12) = k4_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_9,plain,(
    ! [X9] : k2_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_10,plain,(
    ! [X3,X4] : k2_xboole_0(X3,X4) = k2_xboole_0(X4,X3) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_12,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_16,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_12]),
    [final]).

cnf(c_0_17,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14]),
    [final]).

fof(c_0_18,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_19,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | ~ r2_xboole_0(X5,X6) )
      & ( X5 != X6
        | ~ r2_xboole_0(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | X5 = X6
        | r2_xboole_0(X5,X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_12]),
    [final]).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X1)
    | k4_xboole_0(k1_xboole_0,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_23,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ ( ~ r2_xboole_0(X1,X2)
            & X1 != X2
            & ~ r2_xboole_0(X2,X1) )
      <=> r3_xboole_0(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t104_xboole_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | ~ r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_15]),c_0_22])]),
    [final]).

cnf(c_0_28,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X1)
    | k4_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_14]),
    [final]).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_xboole_0(k2_xboole_0(X1,X2),X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_16]),
    [final]).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r2_xboole_0(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_24]),
    [final]).

fof(c_0_31,negated_conjecture,
    ( ( ~ r2_xboole_0(esk1_0,esk2_0)
      | ~ r3_xboole_0(esk1_0,esk2_0) )
    & ( esk1_0 != esk2_0
      | ~ r3_xboole_0(esk1_0,esk2_0) )
    & ( ~ r2_xboole_0(esk2_0,esk1_0)
      | ~ r3_xboole_0(esk1_0,esk2_0) )
    & ( r2_xboole_0(esk1_0,esk2_0)
      | esk1_0 = esk2_0
      | r2_xboole_0(esk2_0,esk1_0)
      | r3_xboole_0(esk1_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])])).

cnf(c_0_32,plain,
    ( X1 != X2
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_14]),
    [final]).

cnf(c_0_34,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])]),
    [final]).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_xboole_0(k2_xboole_0(X1,X2),X1)
    | k4_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_28]),
    [final]).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | r2_xboole_0(X1,k1_xboole_0)
    | k4_xboole_0(X1,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_13]),
    [final]).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(k2_xboole_0(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_14]),
    [final]).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r2_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_14]),
    [final]).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = k1_xboole_0
    | ~ r2_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_13]),
    [final]).

cnf(c_0_40,plain,
    ( k1_xboole_0 = X1
    | r2_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( r2_xboole_0(esk1_0,esk2_0)
    | esk1_0 = esk2_0
    | r2_xboole_0(esk2_0,esk1_0)
    | r3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_xboole_0(esk2_0,esk1_0)
    | ~ r3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_xboole_0(esk1_0,esk2_0)
    | ~ r3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( esk1_0 != esk2_0
    | ~ r3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_45,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(er,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_13]),c_0_34]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:37:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.026 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # No proof found!
% 0.14/0.38  # SZS status CounterSatisfiable
% 0.14/0.38  # SZS output start Saturation
% 0.14/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.14/0.38  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.14/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.14/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.14/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.38  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.14/0.38  fof(t104_xboole_1, conjecture, ![X1, X2]:(~(((~(r2_xboole_0(X1,X2))&X1!=X2)&~(r2_xboole_0(X2,X1))))<=>r3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_xboole_1)).
% 0.14/0.38  fof(c_0_7, plain, ![X7, X8]:((k4_xboole_0(X7,X8)!=k1_xboole_0|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|k4_xboole_0(X7,X8)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.14/0.38  fof(c_0_8, plain, ![X11, X12]:k4_xboole_0(k2_xboole_0(X11,X12),X12)=k4_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.14/0.38  fof(c_0_9, plain, ![X9]:k2_xboole_0(X9,k1_xboole_0)=X9, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.14/0.38  fof(c_0_10, plain, ![X3, X4]:k2_xboole_0(X3,X4)=k2_xboole_0(X4,X3), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.14/0.38  cnf(c_0_11, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_12, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_13, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_16, plain, (r1_tarski(k2_xboole_0(X1,X2),X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_11, c_0_12]), ['final']).
% 0.14/0.38  cnf(c_0_17, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_13, c_0_14]), ['final']).
% 0.14/0.38  fof(c_0_18, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.38  fof(c_0_19, plain, ![X5, X6]:(((r1_tarski(X5,X6)|~r2_xboole_0(X5,X6))&(X5!=X6|~r2_xboole_0(X5,X6)))&(~r1_tarski(X5,X6)|X5=X6|r2_xboole_0(X5,X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.14/0.38  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(k2_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_15, c_0_12]), ['final']).
% 0.14/0.38  cnf(c_0_21, plain, (r1_tarski(X1,X1)|k4_xboole_0(k1_xboole_0,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.38  cnf(c_0_22, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.14/0.38  cnf(c_0_23, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.14/0.38  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.14/0.38  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(~(((~(r2_xboole_0(X1,X2))&X1!=X2)&~(r2_xboole_0(X2,X1))))<=>r3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t104_xboole_1])).
% 0.14/0.38  cnf(c_0_26, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0|~r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_20, c_0_17])).
% 0.14/0.38  cnf(c_0_27, plain, (r1_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_15]), c_0_22])]), ['final']).
% 0.14/0.38  cnf(c_0_28, plain, (r1_tarski(k2_xboole_0(X1,X2),X1)|k4_xboole_0(X2,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=X2|r2_xboole_0(k2_xboole_0(X1,X2),X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_16]), ['final']).
% 0.14/0.38  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r2_xboole_0(k2_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_20, c_0_24]), ['final']).
% 0.14/0.38  fof(c_0_31, negated_conjecture, ((((~r2_xboole_0(esk1_0,esk2_0)|~r3_xboole_0(esk1_0,esk2_0))&(esk1_0!=esk2_0|~r3_xboole_0(esk1_0,esk2_0)))&(~r2_xboole_0(esk2_0,esk1_0)|~r3_xboole_0(esk1_0,esk2_0)))&(r2_xboole_0(esk1_0,esk2_0)|esk1_0=esk2_0|r2_xboole_0(esk2_0,esk1_0)|r3_xboole_0(esk1_0,esk2_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])])).
% 0.14/0.38  cnf(c_0_32, plain, (X1!=X2|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_33, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_12, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_34, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27])]), ['final']).
% 0.14/0.38  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=X1|r2_xboole_0(k2_xboole_0(X1,X2),X1)|k4_xboole_0(X2,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_28]), ['final']).
% 0.14/0.38  cnf(c_0_36, plain, (X1=k1_xboole_0|r2_xboole_0(X1,k1_xboole_0)|k4_xboole_0(X1,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_13]), ['final']).
% 0.14/0.38  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(k2_xboole_0(X2,X1),X2)), inference(spm,[status(thm)],[c_0_20, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r2_xboole_0(k2_xboole_0(X2,X1),X2)), inference(spm,[status(thm)],[c_0_30, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_39, plain, (k4_xboole_0(X1,k1_xboole_0)=k1_xboole_0|~r2_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_13]), ['final']).
% 0.14/0.38  cnf(c_0_40, plain, (k1_xboole_0=X1|r2_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_22]), ['final']).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (r2_xboole_0(esk1_0,esk2_0)|esk1_0=esk2_0|r2_xboole_0(esk2_0,esk1_0)|r3_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (~r2_xboole_0(esk2_0,esk1_0)|~r3_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (~r2_xboole_0(esk1_0,esk2_0)|~r3_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (esk1_0!=esk2_0|~r3_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.14/0.38  cnf(c_0_45, plain, (~r2_xboole_0(X1,X1)), inference(er,[status(thm)],[c_0_32]), ['final']).
% 0.14/0.38  cnf(c_0_46, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_13]), c_0_34]), ['final']).
% 0.14/0.38  # SZS output end Saturation
% 0.14/0.38  # Proof object total steps             : 47
% 0.14/0.38  # Proof object clause steps            : 32
% 0.14/0.38  # Proof object formula steps           : 15
% 0.14/0.38  # Proof object conjectures             : 7
% 0.14/0.38  # Proof object clause conjectures      : 4
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 13
% 0.14/0.38  # Proof object initial formulas used   : 7
% 0.14/0.38  # Proof object generating inferences   : 17
% 0.14/0.38  # Proof object simplifying inferences  : 6
% 0.14/0.38  # Parsed axioms                        : 7
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 13
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 13
% 0.14/0.38  # Processed clauses                    : 79
% 0.14/0.38  # ...of these trivial                  : 3
% 0.14/0.38  # ...subsumed                          : 30
% 0.14/0.38  # ...remaining for further processing  : 46
% 0.14/0.38  # Other redundant clauses eliminated   : 1
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 3
% 0.14/0.38  # Generated clauses                    : 78
% 0.14/0.38  # ...of the previous two non-trivial   : 53
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 77
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 1
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
% 0.14/0.38  # Current number of processed clauses  : 29
% 0.14/0.38  #    Positive orientable unit clauses  : 8
% 0.14/0.38  #    Positive unorientable unit clauses: 1
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 19
% 0.14/0.38  # Current number of unprocessed clauses: 0
% 0.14/0.38  # ...number of literals in the above   : 0
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 16
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 83
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 70
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 28
% 0.14/0.38  # Unit Clause-clause subsumption calls : 12
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 16
% 0.14/0.38  # BW rewrite match successes           : 6
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1307
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.029 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.032 s
% 0.14/0.38  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
