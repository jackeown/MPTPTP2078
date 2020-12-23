%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:17 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   64 (1015 expanded)
%              Number of clauses        :   39 ( 420 expanded)
%              Number of leaves         :   12 ( 297 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 (1342 expanded)
%              Number of equality atoms :   87 (1131 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
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

fof(t10_setfam_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(X1,X2)) != k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t19_zfmisc_1,axiom,(
    ! [X1,X2] : k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(t12_setfam_1,conjecture,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_12,plain,(
    ! [X5,X6] :
      ( ( ~ r1_xboole_0(X5,X6)
        | k3_xboole_0(X5,X6) = k1_xboole_0 )
      & ( k3_xboole_0(X5,X6) != k1_xboole_0
        | r1_xboole_0(X5,X6) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_13,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X34,X35] :
      ( X34 = k1_xboole_0
      | X35 = k1_xboole_0
      | k1_setfam_1(k2_xboole_0(X34,X35)) = k3_xboole_0(k1_setfam_1(X34),k1_setfam_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X24,X25] : k2_tarski(X24,X25) = k2_xboole_0(k1_tarski(X24),k1_tarski(X25)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_19,plain,(
    ! [X26] : k2_tarski(X26,X26) = k1_tarski(X26) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X27,X28] : k1_enumset1(X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X29,X30,X31] : k2_enumset1(X29,X29,X30,X31) = k1_enumset1(X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X36] : k1_setfam_1(k1_tarski(X36)) = X36 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

fof(c_0_23,plain,(
    ! [X32,X33] : k3_xboole_0(k1_tarski(X32),k2_tarski(X32,X33)) = k1_tarski(X32) ),
    inference(variable_rename,[status(thm)],[t19_zfmisc_1])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r1_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))
    | k1_setfam_1(k2_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_34,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))) = k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_16])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | k2_enumset1(X2,X2,X2,X2) = k1_xboole_0
    | r1_xboole_0(X2,X1)
    | k1_setfam_1(k2_enumset1(X2,X2,X2,X1)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_34])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t12_setfam_1])).

fof(c_0_38,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r1_xboole_0(X7,X8)
        | r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X12,k3_xboole_0(X10,X11))
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_39,plain,
    ( r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_35])).

cnf(c_0_40,plain,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_34])])).

fof(c_0_41,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X18,X17)
        | X18 = X15
        | X18 = X16
        | X17 != k2_tarski(X15,X16) )
      & ( X19 != X15
        | r2_hidden(X19,X17)
        | X17 != k2_tarski(X15,X16) )
      & ( X19 != X16
        | r2_hidden(X19,X17)
        | X17 != k2_tarski(X15,X16) )
      & ( esk2_3(X20,X21,X22) != X20
        | ~ r2_hidden(esk2_3(X20,X21,X22),X22)
        | X22 = k2_tarski(X20,X21) )
      & ( esk2_3(X20,X21,X22) != X21
        | ~ r2_hidden(esk2_3(X20,X21,X22),X22)
        | X22 = k2_tarski(X20,X21) )
      & ( r2_hidden(esk2_3(X20,X21,X22),X22)
        | esk2_3(X20,X21,X22) = X20
        | esk2_3(X20,X21,X22) = X21
        | X22 = k2_tarski(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_42,negated_conjecture,(
    k1_setfam_1(k2_tarski(esk3_0,esk4_0)) != k3_xboole_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( r1_xboole_0(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk3_0,esk4_0)) != k3_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),X2)) = k1_setfam_1(k2_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
    | k2_enumset1(X2,X2,X2,X2) = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_34])).

cnf(c_0_50,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_16])).

cnf(c_0_51,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_40])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_16])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_46,c_0_16])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_28]),c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) != k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_28]),c_0_29]),c_0_16])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | k2_enumset1(X2,X2,X2,X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).

cnf(c_0_60,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_62]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:45:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.47/0.70  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.47/0.70  # and selection function SelectNegativeLiterals.
% 0.47/0.70  #
% 0.47/0.70  # Preprocessing time       : 0.025 s
% 0.47/0.70  # Presaturation interreduction done
% 0.47/0.70  
% 0.47/0.70  # Proof found!
% 0.47/0.70  # SZS status Theorem
% 0.47/0.70  # SZS output start CNFRefutation
% 0.47/0.70  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.47/0.70  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.47/0.70  fof(t10_setfam_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&k1_setfam_1(k2_xboole_0(X1,X2))!=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 0.47/0.70  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.47/0.70  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.47/0.70  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.47/0.70  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.47/0.70  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.47/0.70  fof(t19_zfmisc_1, axiom, ![X1, X2]:k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 0.47/0.70  fof(t12_setfam_1, conjecture, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.47/0.70  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.47/0.70  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.47/0.70  fof(c_0_12, plain, ![X5, X6]:((~r1_xboole_0(X5,X6)|k3_xboole_0(X5,X6)=k1_xboole_0)&(k3_xboole_0(X5,X6)!=k1_xboole_0|r1_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.47/0.70  fof(c_0_13, plain, ![X13, X14]:k4_xboole_0(X13,k4_xboole_0(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.47/0.70  fof(c_0_14, plain, ![X34, X35]:(X34=k1_xboole_0|X35=k1_xboole_0|k1_setfam_1(k2_xboole_0(X34,X35))=k3_xboole_0(k1_setfam_1(X34),k1_setfam_1(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).
% 0.47/0.70  cnf(c_0_15, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.70  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.70  cnf(c_0_17, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.70  fof(c_0_18, plain, ![X24, X25]:k2_tarski(X24,X25)=k2_xboole_0(k1_tarski(X24),k1_tarski(X25)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.47/0.70  fof(c_0_19, plain, ![X26]:k2_tarski(X26,X26)=k1_tarski(X26), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.47/0.70  fof(c_0_20, plain, ![X27, X28]:k1_enumset1(X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.47/0.70  fof(c_0_21, plain, ![X29, X30, X31]:k2_enumset1(X29,X29,X30,X31)=k1_enumset1(X29,X30,X31), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.47/0.70  fof(c_0_22, plain, ![X36]:k1_setfam_1(k1_tarski(X36))=X36, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 0.47/0.70  fof(c_0_23, plain, ![X32, X33]:k3_xboole_0(k1_tarski(X32),k2_tarski(X32,X33))=k1_tarski(X32), inference(variable_rename,[status(thm)],[t19_zfmisc_1])).
% 0.47/0.70  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.47/0.70  cnf(c_0_25, plain, (X2=k1_xboole_0|X1=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), inference(rw,[status(thm)],[c_0_17, c_0_16])).
% 0.47/0.70  cnf(c_0_26, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.70  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.70  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.70  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.70  cnf(c_0_30, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.47/0.70  cnf(c_0_31, plain, (k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.47/0.70  cnf(c_0_32, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r1_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))|k1_setfam_1(k2_xboole_0(X1,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.47/0.70  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X1,X2)=k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29])).
% 0.47/0.70  cnf(c_0_34, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_27]), c_0_28]), c_0_29])).
% 0.47/0.70  cnf(c_0_35, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)))=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_16])).
% 0.47/0.70  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|k2_enumset1(X2,X2,X2,X2)=k1_xboole_0|r1_xboole_0(X2,X1)|k1_setfam_1(k2_enumset1(X2,X2,X2,X1))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_34])).
% 0.47/0.70  fof(c_0_37, negated_conjecture, ~(![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t12_setfam_1])).
% 0.47/0.70  fof(c_0_38, plain, ![X7, X8, X10, X11, X12]:((r1_xboole_0(X7,X8)|r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)))&(~r2_hidden(X12,k3_xboole_0(X10,X11))|~r1_xboole_0(X10,X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.47/0.70  cnf(c_0_39, plain, (r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))|k2_enumset1(X1,X1,X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_35])).
% 0.47/0.70  cnf(c_0_40, plain, (k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)=k1_xboole_0|r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_34])])).
% 0.47/0.70  fof(c_0_41, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X18,X17)|(X18=X15|X18=X16)|X17!=k2_tarski(X15,X16))&((X19!=X15|r2_hidden(X19,X17)|X17!=k2_tarski(X15,X16))&(X19!=X16|r2_hidden(X19,X17)|X17!=k2_tarski(X15,X16))))&(((esk2_3(X20,X21,X22)!=X20|~r2_hidden(esk2_3(X20,X21,X22),X22)|X22=k2_tarski(X20,X21))&(esk2_3(X20,X21,X22)!=X21|~r2_hidden(esk2_3(X20,X21,X22),X22)|X22=k2_tarski(X20,X21)))&(r2_hidden(esk2_3(X20,X21,X22),X22)|(esk2_3(X20,X21,X22)=X20|esk2_3(X20,X21,X22)=X21)|X22=k2_tarski(X20,X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.47/0.70  fof(c_0_42, negated_conjecture, k1_setfam_1(k2_tarski(esk3_0,esk4_0))!=k3_xboole_0(esk3_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).
% 0.47/0.70  cnf(c_0_43, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.47/0.70  cnf(c_0_44, plain, (r1_xboole_0(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))|r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.47/0.70  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.70  cnf(c_0_46, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.47/0.70  cnf(c_0_47, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.47/0.70  cnf(c_0_48, negated_conjecture, (k1_setfam_1(k2_tarski(esk3_0,esk4_0))!=k3_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.47/0.70  cnf(c_0_49, plain, (k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),X2))=k1_setfam_1(k2_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))|k2_enumset1(X2,X2,X2,X2)=k1_xboole_0|X1=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_34])).
% 0.47/0.70  cnf(c_0_50, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_43, c_0_16])).
% 0.47/0.70  cnf(c_0_51, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_40])).
% 0.47/0.70  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_16])).
% 0.47/0.70  cnf(c_0_53, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_46, c_0_16])).
% 0.47/0.70  cnf(c_0_54, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_28]), c_0_29])).
% 0.47/0.70  cnf(c_0_55, negated_conjecture, (k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))!=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_28]), c_0_29]), c_0_16])).
% 0.47/0.70  cnf(c_0_56, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|k2_enumset1(X2,X2,X2,X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_33]), c_0_34]), c_0_34])).
% 0.47/0.70  cnf(c_0_57, plain, (~r2_hidden(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.47/0.70  cnf(c_0_58, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.47/0.70  cnf(c_0_59, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).
% 0.47/0.70  cnf(c_0_60, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.47/0.70  cnf(c_0_61, plain, (~r2_hidden(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_57])).
% 0.47/0.70  cnf(c_0_62, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.47/0.70  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_62]), c_0_61]), ['proof']).
% 0.47/0.70  # SZS output end CNFRefutation
% 0.47/0.70  # Proof object total steps             : 64
% 0.47/0.70  # Proof object clause steps            : 39
% 0.47/0.70  # Proof object formula steps           : 25
% 0.47/0.70  # Proof object conjectures             : 8
% 0.47/0.70  # Proof object clause conjectures      : 5
% 0.47/0.70  # Proof object formula conjectures     : 3
% 0.47/0.70  # Proof object initial clauses used    : 14
% 0.47/0.70  # Proof object initial formulas used   : 12
% 0.47/0.70  # Proof object generating inferences   : 14
% 0.47/0.70  # Proof object simplifying inferences  : 40
% 0.47/0.70  # Training examples: 0 positive, 0 negative
% 0.47/0.70  # Parsed axioms                        : 12
% 0.47/0.70  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.70  # Initial clauses                      : 19
% 0.47/0.70  # Removed in clause preprocessing      : 4
% 0.47/0.70  # Initial clauses in saturation        : 15
% 0.47/0.70  # Processed clauses                    : 866
% 0.47/0.70  # ...of these trivial                  : 4
% 0.47/0.70  # ...subsumed                          : 544
% 0.47/0.70  # ...remaining for further processing  : 318
% 0.47/0.70  # Other redundant clauses eliminated   : 433
% 0.47/0.70  # Clauses deleted for lack of memory   : 0
% 0.47/0.70  # Backward-subsumed                    : 22
% 0.47/0.70  # Backward-rewritten                   : 14
% 0.47/0.70  # Generated clauses                    : 17771
% 0.47/0.70  # ...of the previous two non-trivial   : 16948
% 0.47/0.70  # Contextual simplify-reflections      : 2
% 0.47/0.70  # Paramodulations                      : 17246
% 0.47/0.70  # Factorizations                       : 93
% 0.47/0.70  # Equation resolutions                 : 433
% 0.47/0.70  # Propositional unsat checks           : 0
% 0.47/0.70  #    Propositional check models        : 0
% 0.47/0.70  #    Propositional check unsatisfiable : 0
% 0.47/0.70  #    Propositional clauses             : 0
% 0.47/0.70  #    Propositional clauses after purity: 0
% 0.47/0.70  #    Propositional unsat core size     : 0
% 0.47/0.70  #    Propositional preprocessing time  : 0.000
% 0.47/0.70  #    Propositional encoding time       : 0.000
% 0.47/0.70  #    Propositional solver time         : 0.000
% 0.47/0.70  #    Success case prop preproc time    : 0.000
% 0.47/0.70  #    Success case prop encoding time   : 0.000
% 0.47/0.70  #    Success case prop solver time     : 0.000
% 0.47/0.70  # Current number of processed clauses  : 263
% 0.47/0.70  #    Positive orientable unit clauses  : 10
% 0.47/0.70  #    Positive unorientable unit clauses: 0
% 0.47/0.70  #    Negative unit clauses             : 2
% 0.47/0.70  #    Non-unit-clauses                  : 251
% 0.47/0.70  # Current number of unprocessed clauses: 16022
% 0.47/0.70  # ...number of literals in the above   : 117366
% 0.47/0.70  # Current number of archived formulas  : 0
% 0.47/0.70  # Current number of archived clauses   : 56
% 0.47/0.70  # Clause-clause subsumption calls (NU) : 9725
% 0.47/0.70  # Rec. Clause-clause subsumption calls : 2963
% 0.47/0.70  # Non-unit clause-clause subsumptions  : 413
% 0.47/0.70  # Unit Clause-clause subsumption calls : 72
% 0.47/0.70  # Rewrite failures with RHS unbound    : 0
% 0.47/0.70  # BW rewrite match attempts            : 17
% 0.47/0.70  # BW rewrite match successes           : 6
% 0.47/0.70  # Condensation attempts                : 0
% 0.47/0.70  # Condensation successes               : 0
% 0.47/0.70  # Termbank termtop insertions          : 666527
% 0.54/0.70  
% 0.54/0.70  # -------------------------------------------------
% 0.54/0.70  # User time                : 0.336 s
% 0.54/0.70  # System time              : 0.021 s
% 0.54/0.70  # Total time               : 0.358 s
% 0.54/0.70  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
