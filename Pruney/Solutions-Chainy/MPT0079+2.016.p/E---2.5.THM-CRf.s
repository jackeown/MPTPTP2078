%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:02 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 577 expanded)
%              Number of clauses        :   49 ( 246 expanded)
%              Number of leaves         :   12 ( 160 expanded)
%              Depth                    :   13
%              Number of atoms          :   89 ( 712 expanded)
%              Number of equality atoms :   75 ( 609 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ( ~ r1_xboole_0(X9,X10)
        | k3_xboole_0(X9,X10) = k1_xboole_0 )
      & ( k3_xboole_0(X9,X10) != k1_xboole_0
        | r1_xboole_0(X9,X10) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_13,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_15,plain,(
    ! [X29,X30] : k2_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(X29,X30)) = X29 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = k2_xboole_0(esk4_0,esk5_0)
    & r1_xboole_0(esk4_0,esk2_0)
    & r1_xboole_0(esk5_0,esk3_0)
    & esk4_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_19,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_21,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k4_xboole_0(X20,X19)) = k2_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_22,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X17] : k2_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X22,X23,X24] : k4_xboole_0(k4_xboole_0(X22,X23),X24) = k4_xboole_0(X22,k2_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_27])).

fof(c_0_34,plain,(
    ! [X25,X26] : k4_xboole_0(X25,k2_xboole_0(X25,X26)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_35,plain,(
    ! [X18] : k3_xboole_0(X18,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_17]),c_0_17])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk3_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_31]),c_0_32]),c_0_27]),c_0_33])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = k2_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X21] : k4_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_36]),c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,X1)) = k4_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = k2_xboole_0(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_17])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_44]),c_0_32]),c_0_27]),c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk5_0,k2_xboole_0(X1,esk3_0)) = k4_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_27])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_37]),c_0_27]),c_0_33])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk4_0,X1)) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk5_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_47]),c_0_40])).

cnf(c_0_59,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(esk3_0,esk5_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_32])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk5_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_39]),c_0_55]),c_0_32])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(X1,esk4_0)) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_27])).

cnf(c_0_62,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,esk5_0),esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_57]),c_0_32]),c_0_27])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_58]),c_0_49])).

cnf(c_0_64,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk2_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_50]),c_0_55]),c_0_32])).

cnf(c_0_66,negated_conjecture,
    ( esk5_0 = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_50]),c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk2_0,X1)) = k4_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = k2_xboole_0(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_67]),c_0_49])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_68]),c_0_55])).

cnf(c_0_72,negated_conjecture,
    ( esk4_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_49]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___024_B31_F1_PI_AE_Q4_CS_SP_S2S
% 0.20/0.40  # and selection function SelectNewComplexAHP.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.026 s
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.40  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.20/0.40  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.20/0.40  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.40  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.40  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.40  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.40  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.20/0.40  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.20/0.40  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.40  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.40  fof(c_0_12, plain, ![X9, X10]:((~r1_xboole_0(X9,X10)|k3_xboole_0(X9,X10)=k1_xboole_0)&(k3_xboole_0(X9,X10)!=k1_xboole_0|r1_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.40  fof(c_0_13, plain, ![X27, X28]:k4_xboole_0(X27,k4_xboole_0(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.40  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 0.20/0.40  fof(c_0_15, plain, ![X29, X30]:k2_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(X29,X30))=X29, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.20/0.40  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  fof(c_0_18, negated_conjecture, (((k2_xboole_0(esk2_0,esk3_0)=k2_xboole_0(esk4_0,esk5_0)&r1_xboole_0(esk4_0,esk2_0))&r1_xboole_0(esk5_0,esk3_0))&esk4_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.40  cnf(c_0_19, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  fof(c_0_20, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.40  fof(c_0_21, plain, ![X19, X20]:k2_xboole_0(X19,k4_xboole_0(X20,X19))=k2_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.40  fof(c_0_22, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.40  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.40  cnf(c_0_24, negated_conjecture, (r1_xboole_0(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  fof(c_0_25, plain, ![X17]:k2_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.40  cnf(c_0_26, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_19, c_0_17])).
% 0.20/0.40  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_28, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  fof(c_0_30, plain, ![X22, X23, X24]:k4_xboole_0(k4_xboole_0(X22,X23),X24)=k4_xboole_0(X22,k2_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.40  cnf(c_0_32, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_33, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_27])).
% 0.20/0.40  fof(c_0_34, plain, ![X25, X26]:k4_xboole_0(X25,k2_xboole_0(X25,X26))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.20/0.40  fof(c_0_35, plain, ![X18]:k3_xboole_0(X18,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (r1_xboole_0(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_17]), c_0_17])).
% 0.20/0.40  cnf(c_0_38, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (k4_xboole_0(esk5_0,esk3_0)=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_31]), c_0_32]), c_0_27]), c_0_33])).
% 0.20/0.40  cnf(c_0_40, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=k2_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_42, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.40  fof(c_0_43, plain, ![X21]:k4_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_36]), c_0_37])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,X1))=k4_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.40  cnf(c_0_46, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_27])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=k2_xboole_0(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_41, c_0_27])).
% 0.20/0.40  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_42, c_0_17])).
% 0.20/0.40  cnf(c_0_49, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.40  cnf(c_0_50, negated_conjecture, (k4_xboole_0(esk2_0,esk4_0)=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_44]), c_0_32]), c_0_27]), c_0_33])).
% 0.20/0.40  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk5_0,k2_xboole_0(X1,esk3_0))=k4_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_45, c_0_27])).
% 0.20/0.40  cnf(c_0_52, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_28, c_0_38])).
% 0.20/0.40  cnf(c_0_53, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.40  cnf(c_0_54, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_37]), c_0_27]), c_0_33])).
% 0.20/0.40  cnf(c_0_55, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk4_0,X1))=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_50])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk5_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_47])).
% 0.20/0.40  cnf(c_0_58, negated_conjecture, (k4_xboole_0(esk5_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_47]), c_0_40])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(esk3_0,esk5_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_32])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (k4_xboole_0(esk3_0,esk5_0)=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_39]), c_0_55]), c_0_32])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(X1,esk4_0))=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_56, c_0_27])).
% 0.20/0.40  cnf(c_0_62, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,esk5_0),esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_57]), c_0_32]), c_0_27])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk5_0))=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_58]), c_0_49])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (k2_xboole_0(esk4_0,esk3_0)=esk4_0), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk4_0,esk2_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_50]), c_0_55]), c_0_32])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (esk5_0=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_50]), c_0_63])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_64])).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk2_0,X1))=k4_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_65])).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=k2_xboole_0(esk2_0,esk4_0)), inference(rw,[status(thm)],[c_0_47, c_0_66])).
% 0.20/0.40  cnf(c_0_70, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_67]), c_0_49])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_68]), c_0_55])).
% 0.20/0.40  cnf(c_0_72, negated_conjecture, (esk4_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71]), c_0_49]), c_0_72]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 74
% 0.20/0.40  # Proof object clause steps            : 49
% 0.20/0.40  # Proof object formula steps           : 25
% 0.20/0.40  # Proof object conjectures             : 32
% 0.20/0.40  # Proof object clause conjectures      : 29
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 15
% 0.20/0.40  # Proof object initial formulas used   : 12
% 0.20/0.40  # Proof object generating inferences   : 24
% 0.20/0.40  # Proof object simplifying inferences  : 38
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 13
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 18
% 0.20/0.40  # Removed in clause preprocessing      : 1
% 0.20/0.40  # Initial clauses in saturation        : 17
% 0.20/0.40  # Processed clauses                    : 339
% 0.20/0.40  # ...of these trivial                  : 77
% 0.20/0.40  # ...subsumed                          : 95
% 0.20/0.40  # ...remaining for further processing  : 167
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 71
% 0.20/0.40  # Generated clauses                    : 2168
% 0.20/0.40  # ...of the previous two non-trivial   : 1359
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 2151
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 2
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 91
% 0.20/0.40  #    Positive orientable unit clauses  : 55
% 0.20/0.40  #    Positive unorientable unit clauses: 4
% 0.20/0.40  #    Negative unit clauses             : 3
% 0.20/0.40  #    Non-unit-clauses                  : 29
% 0.20/0.40  # Current number of unprocessed clauses: 1016
% 0.20/0.40  # ...number of literals in the above   : 1419
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 72
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 1135
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 778
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 76
% 0.20/0.40  # Unit Clause-clause subsumption calls : 20
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 39
% 0.20/0.40  # BW rewrite match successes           : 22
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 21680
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.050 s
% 0.20/0.40  # System time              : 0.005 s
% 0.20/0.40  # Total time               : 0.055 s
% 0.20/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
