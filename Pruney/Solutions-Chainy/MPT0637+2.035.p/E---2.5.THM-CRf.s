%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:29 EST 2020

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 808 expanded)
%              Number of clauses        :   56 ( 363 expanded)
%              Number of leaves         :   18 ( 222 expanded)
%              Depth                    :   14
%              Number of atoms          :  163 ( 979 expanded)
%              Number of equality atoms :   70 ( 739 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(c_0_18,plain,(
    ! [X17,X18] : k1_setfam_1(k2_tarski(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_19,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | k1_relat_1(k7_relat_1(X36,X35)) = k3_xboole_0(k1_relat_1(X36),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_25,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_26,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | v1_relat_1(k3_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_31,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_27]),c_0_28])).

fof(c_0_35,plain,(
    ! [X29] :
      ( k1_relat_1(k6_relat_1(X29)) = X29
      & k2_relat_1(k6_relat_1(X29)) = X29 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_36,plain,(
    ! [X19] : v1_relat_1(k6_relat_1(X19)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_37,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_setfam_1(k2_enumset1(X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2)) = k1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_27]),c_0_28])).

fof(c_0_44,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_27]),c_0_28])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_34]),c_0_34])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

fof(c_0_48,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | k7_relat_1(X38,X37) = k5_relat_1(k6_relat_1(X37),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_49,plain,
    ( v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_43,c_0_34])).

fof(c_0_50,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).

fof(c_0_51,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ r1_tarski(k2_relat_1(X25),X24)
      | k8_relat_1(X24,X25) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_52,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_45,c_0_34])).

cnf(c_0_53,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47])).

cnf(c_0_54,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_46])).

fof(c_0_56,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r1_tarski(k1_relat_1(X33),X32)
      | k5_relat_1(k6_relat_1(X32),X33) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

cnf(c_0_57,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_58,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_59,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | k8_relat_1(X22,X23) = k5_relat_1(X23,k6_relat_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

cnf(c_0_60,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1) ),
    inference(rw,[status(thm)],[c_0_52,c_0_47])).

cnf(c_0_63,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_42])])).

cnf(c_0_64,plain,
    ( v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[c_0_55,c_0_47])).

cnf(c_0_65,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_27]),c_0_28])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_68,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X26)
      | ~ v1_relat_1(X27)
      | ~ v1_relat_1(X28)
      | k5_relat_1(k5_relat_1(X26,X27),X28) = k5_relat_1(X26,k5_relat_1(X27,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_69,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_42])])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_54]),c_0_42])])).

cnf(c_0_72,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(X1)),k6_relat_1(X2))) = k1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_47]),c_0_63])).

cnf(c_0_73,plain,
    ( v1_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_54]),c_0_42])])).

cnf(c_0_74,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_41]),c_0_42])])).

fof(c_0_75,plain,(
    ! [X30,X31] :
      ( ( r1_tarski(k5_relat_1(X31,k6_relat_1(X30)),X31)
        | ~ v1_relat_1(X31) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X30),X31),X31)
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

cnf(c_0_76,negated_conjecture,
    ( k6_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_34])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_78,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_42])])).

cnf(c_0_80,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_41])).

cnf(c_0_82,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( k6_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_76,c_0_46])).

cnf(c_0_84,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_77])).

cnf(c_0_85,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),X3)) = k5_relat_1(k6_relat_1(X1),X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_42]),c_0_42])])).

cnf(c_0_86,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_54])).

cnf(c_0_87,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_83,c_0_47])).

cnf(c_0_89,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))),X2) = k5_relat_1(k6_relat_1(X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_88,c_0_63])).

cnf(c_0_91,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_89]),c_0_71]),c_0_42])])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:24:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 1.07/1.32  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.07/1.32  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.07/1.32  #
% 1.07/1.32  # Preprocessing time       : 0.027 s
% 1.07/1.32  # Presaturation interreduction done
% 1.07/1.32  
% 1.07/1.32  # Proof found!
% 1.07/1.32  # SZS status Theorem
% 1.07/1.32  # SZS output start CNFRefutation
% 1.07/1.32  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.07/1.32  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.07/1.32  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 1.07/1.32  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.07/1.32  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.07/1.32  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.07/1.32  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.07/1.32  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.07/1.32  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.07/1.32  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.07/1.32  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.07/1.32  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.07/1.32  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.07/1.32  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 1.07/1.32  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.07/1.32  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 1.07/1.32  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 1.07/1.32  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 1.07/1.32  fof(c_0_18, plain, ![X17, X18]:k1_setfam_1(k2_tarski(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 1.07/1.32  fof(c_0_19, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.07/1.32  fof(c_0_20, plain, ![X35, X36]:(~v1_relat_1(X36)|k1_relat_1(k7_relat_1(X36,X35))=k3_xboole_0(k1_relat_1(X36),X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 1.07/1.32  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.07/1.32  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.07/1.32  fof(c_0_23, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.07/1.32  fof(c_0_24, plain, ![X10, X11]:k4_xboole_0(X10,k4_xboole_0(X10,X11))=k3_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.07/1.32  fof(c_0_25, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.07/1.32  cnf(c_0_26, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.07/1.32  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 1.07/1.32  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.07/1.32  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.07/1.32  fof(c_0_30, plain, ![X20, X21]:(~v1_relat_1(X20)|v1_relat_1(k3_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 1.07/1.32  fof(c_0_31, plain, ![X8, X9]:r1_tarski(k3_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.07/1.32  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.07/1.32  cnf(c_0_33, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 1.07/1.32  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_27]), c_0_28])).
% 1.07/1.32  fof(c_0_35, plain, ![X29]:(k1_relat_1(k6_relat_1(X29))=X29&k2_relat_1(k6_relat_1(X29))=X29), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 1.07/1.32  fof(c_0_36, plain, ![X19]:v1_relat_1(k6_relat_1(X19)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 1.07/1.32  cnf(c_0_37, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.07/1.32  cnf(c_0_38, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.07/1.32  cnf(c_0_39, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_setfam_1(k2_enumset1(X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 1.07/1.32  cnf(c_0_40, plain, (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2))=k1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 1.07/1.32  cnf(c_0_41, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.07/1.32  cnf(c_0_42, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.07/1.32  cnf(c_0_43, plain, (v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_27]), c_0_28])).
% 1.07/1.32  fof(c_0_44, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 1.07/1.32  cnf(c_0_45, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_27]), c_0_28])).
% 1.07/1.32  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_34]), c_0_34])).
% 1.07/1.32  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 1.07/1.32  fof(c_0_48, plain, ![X37, X38]:(~v1_relat_1(X38)|k7_relat_1(X38,X37)=k5_relat_1(k6_relat_1(X37),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 1.07/1.32  cnf(c_0_49, plain, (v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_43, c_0_34])).
% 1.07/1.32  fof(c_0_50, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).
% 1.07/1.32  fof(c_0_51, plain, ![X24, X25]:(~v1_relat_1(X25)|(~r1_tarski(k2_relat_1(X25),X24)|k8_relat_1(X24,X25)=X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 1.07/1.32  cnf(c_0_52, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_45, c_0_34])).
% 1.07/1.32  cnf(c_0_53, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47])).
% 1.07/1.32  cnf(c_0_54, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.07/1.32  cnf(c_0_55, plain, (v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_49, c_0_46])).
% 1.07/1.32  fof(c_0_56, plain, ![X32, X33]:(~v1_relat_1(X33)|(~r1_tarski(k1_relat_1(X33),X32)|k5_relat_1(k6_relat_1(X32),X33)=X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 1.07/1.32  cnf(c_0_57, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.07/1.32  fof(c_0_58, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.07/1.32  fof(c_0_59, plain, ![X22, X23]:(~v1_relat_1(X23)|k8_relat_1(X22,X23)=k5_relat_1(X23,k6_relat_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 1.07/1.32  cnf(c_0_60, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.07/1.32  cnf(c_0_61, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.07/1.32  cnf(c_0_62, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)), inference(rw,[status(thm)],[c_0_52, c_0_47])).
% 1.07/1.32  cnf(c_0_63, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_42])])).
% 1.07/1.32  cnf(c_0_64, plain, (v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))|~v1_relat_1(X2)), inference(rw,[status(thm)],[c_0_55, c_0_47])).
% 1.07/1.32  cnf(c_0_65, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.07/1.32  cnf(c_0_66, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_27]), c_0_28])).
% 1.07/1.32  cnf(c_0_67, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.07/1.32  fof(c_0_68, plain, ![X26, X27, X28]:(~v1_relat_1(X26)|(~v1_relat_1(X27)|(~v1_relat_1(X28)|k5_relat_1(k5_relat_1(X26,X27),X28)=k5_relat_1(X26,k5_relat_1(X27,X28))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 1.07/1.32  cnf(c_0_69, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 1.07/1.32  cnf(c_0_70, plain, (k8_relat_1(X1,k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_42])])).
% 1.07/1.32  cnf(c_0_71, plain, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_54]), c_0_42])])).
% 1.07/1.32  cnf(c_0_72, plain, (k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(X1)),k6_relat_1(X2)))=k1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_47]), c_0_63])).
% 1.07/1.32  cnf(c_0_73, plain, (v1_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_54]), c_0_42])])).
% 1.07/1.32  cnf(c_0_74, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_41]), c_0_42])])).
% 1.07/1.32  fof(c_0_75, plain, ![X30, X31]:((r1_tarski(k5_relat_1(X31,k6_relat_1(X30)),X31)|~v1_relat_1(X31))&(r1_tarski(k5_relat_1(k6_relat_1(X30),X31),X31)|~v1_relat_1(X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 1.07/1.32  cnf(c_0_76, negated_conjecture, (k6_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_66, c_0_34])).
% 1.07/1.32  cnf(c_0_77, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_67])).
% 1.07/1.32  cnf(c_0_78, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 1.07/1.32  cnf(c_0_79, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_42])])).
% 1.07/1.32  cnf(c_0_80, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 1.07/1.32  cnf(c_0_81, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_41])).
% 1.07/1.32  cnf(c_0_82, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 1.07/1.32  cnf(c_0_83, negated_conjecture, (k6_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_76, c_0_46])).
% 1.07/1.32  cnf(c_0_84, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_77])).
% 1.07/1.32  cnf(c_0_85, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),X3))=k5_relat_1(k6_relat_1(X1),X3)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_42]), c_0_42])])).
% 1.07/1.32  cnf(c_0_86, plain, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)),X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_80, c_0_54])).
% 1.07/1.32  cnf(c_0_87, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 1.07/1.32  cnf(c_0_88, negated_conjecture, (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_83, c_0_47])).
% 1.07/1.32  cnf(c_0_89, plain, (k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))),X2)=k5_relat_1(k6_relat_1(X1),X2)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_87])).
% 1.07/1.32  cnf(c_0_90, negated_conjecture, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_88, c_0_63])).
% 1.07/1.32  cnf(c_0_91, plain, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_89]), c_0_71]), c_0_42])])).
% 1.07/1.32  cnf(c_0_92, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])]), ['proof']).
% 1.07/1.32  # SZS output end CNFRefutation
% 1.07/1.32  # Proof object total steps             : 93
% 1.07/1.32  # Proof object clause steps            : 56
% 1.07/1.32  # Proof object formula steps           : 37
% 1.07/1.32  # Proof object conjectures             : 10
% 1.07/1.32  # Proof object clause conjectures      : 7
% 1.07/1.32  # Proof object formula conjectures     : 3
% 1.07/1.32  # Proof object initial clauses used    : 19
% 1.07/1.32  # Proof object initial formulas used   : 18
% 1.07/1.32  # Proof object generating inferences   : 16
% 1.07/1.32  # Proof object simplifying inferences  : 56
% 1.07/1.32  # Training examples: 0 positive, 0 negative
% 1.07/1.32  # Parsed axioms                        : 19
% 1.07/1.32  # Removed by relevancy pruning/SinE    : 0
% 1.07/1.32  # Initial clauses                      : 23
% 1.07/1.32  # Removed in clause preprocessing      : 3
% 1.07/1.32  # Initial clauses in saturation        : 20
% 1.07/1.32  # Processed clauses                    : 3351
% 1.07/1.32  # ...of these trivial                  : 84
% 1.07/1.32  # ...subsumed                          : 2613
% 1.07/1.32  # ...remaining for further processing  : 654
% 1.07/1.32  # Other redundant clauses eliminated   : 2
% 1.07/1.32  # Clauses deleted for lack of memory   : 0
% 1.07/1.32  # Backward-subsumed                    : 42
% 1.07/1.32  # Backward-rewritten                   : 47
% 1.07/1.32  # Generated clauses                    : 82848
% 1.07/1.32  # ...of the previous two non-trivial   : 70923
% 1.07/1.32  # Contextual simplify-reflections      : 73
% 1.07/1.32  # Paramodulations                      : 82846
% 1.07/1.32  # Factorizations                       : 0
% 1.07/1.32  # Equation resolutions                 : 2
% 1.07/1.32  # Propositional unsat checks           : 0
% 1.07/1.32  #    Propositional check models        : 0
% 1.07/1.32  #    Propositional check unsatisfiable : 0
% 1.07/1.32  #    Propositional clauses             : 0
% 1.07/1.32  #    Propositional clauses after purity: 0
% 1.07/1.32  #    Propositional unsat core size     : 0
% 1.07/1.32  #    Propositional preprocessing time  : 0.000
% 1.07/1.32  #    Propositional encoding time       : 0.000
% 1.07/1.32  #    Propositional solver time         : 0.000
% 1.07/1.32  #    Success case prop preproc time    : 0.000
% 1.07/1.32  #    Success case prop encoding time   : 0.000
% 1.07/1.32  #    Success case prop solver time     : 0.000
% 1.07/1.32  # Current number of processed clauses  : 544
% 1.07/1.32  #    Positive orientable unit clauses  : 57
% 1.07/1.32  #    Positive unorientable unit clauses: 1
% 1.07/1.32  #    Negative unit clauses             : 2
% 1.07/1.32  #    Non-unit-clauses                  : 484
% 1.07/1.32  # Current number of unprocessed clauses: 67490
% 1.07/1.32  # ...number of literals in the above   : 297038
% 1.07/1.32  # Current number of archived formulas  : 0
% 1.07/1.32  # Current number of archived clauses   : 111
% 1.07/1.32  # Clause-clause subsumption calls (NU) : 46185
% 1.07/1.32  # Rec. Clause-clause subsumption calls : 32510
% 1.07/1.32  # Non-unit clause-clause subsumptions  : 2666
% 1.07/1.32  # Unit Clause-clause subsumption calls : 40
% 1.07/1.32  # Rewrite failures with RHS unbound    : 0
% 1.07/1.32  # BW rewrite match attempts            : 243
% 1.07/1.32  # BW rewrite match successes           : 78
% 1.07/1.32  # Condensation attempts                : 0
% 1.07/1.32  # Condensation successes               : 0
% 1.07/1.32  # Termbank termtop insertions          : 2107378
% 1.07/1.33  
% 1.07/1.33  # -------------------------------------------------
% 1.07/1.33  # User time                : 0.917 s
% 1.07/1.33  # System time              : 0.051 s
% 1.07/1.33  # Total time               : 0.968 s
% 1.07/1.33  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
