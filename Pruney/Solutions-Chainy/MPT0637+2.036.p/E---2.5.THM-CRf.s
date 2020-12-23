%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:29 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 789 expanded)
%              Number of clauses        :   52 ( 354 expanded)
%              Number of leaves         :   17 ( 217 expanded)
%              Depth                    :   14
%              Number of atoms          :  146 ( 939 expanded)
%              Number of equality atoms :   63 ( 725 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(t78_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(c_0_17,plain,(
    ! [X17,X18] : k1_setfam_1(k2_tarski(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | k1_relat_1(k7_relat_1(X35,X34)) = k3_xboole_0(k1_relat_1(X35),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_24,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_25,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | v1_relat_1(k3_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_30,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_26]),c_0_27])).

fof(c_0_34,plain,(
    ! [X25] :
      ( k1_relat_1(k6_relat_1(X25)) = X25
      & k2_relat_1(k6_relat_1(X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_35,plain,(
    ! [X19] : v1_relat_1(k6_relat_1(X19)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_36,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_setfam_1(k2_enumset1(X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2)) = k1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_26]),c_0_27])).

fof(c_0_43,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_26]),c_0_27])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_33]),c_0_33])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

fof(c_0_47,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | k7_relat_1(X37,X36) = k5_relat_1(k6_relat_1(X36),X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_48,plain,
    ( v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_42,c_0_33])).

fof(c_0_49,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).

cnf(c_0_50,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_44,c_0_33])).

cnf(c_0_51,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_46])).

cnf(c_0_52,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_45])).

fof(c_0_54,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ r1_tarski(k1_relat_1(X29),X28)
      | k5_relat_1(k6_relat_1(X28),X29) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

cnf(c_0_55,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_56,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ r1_tarski(k2_relat_1(X32),X31)
      | k5_relat_1(X32,k6_relat_1(X31)) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1) ),
    inference(rw,[status(thm)],[c_0_50,c_0_46])).

cnf(c_0_58,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_41])])).

cnf(c_0_59,plain,
    ( v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_46])).

cnf(c_0_60,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_26]),c_0_27])).

fof(c_0_62,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X22)
      | ~ v1_relat_1(X23)
      | ~ v1_relat_1(X24)
      | k5_relat_1(k5_relat_1(X22,X23),X24) = k5_relat_1(X22,k5_relat_1(X23,X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_63,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_52]),c_0_41])])).

cnf(c_0_66,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(X1)),k6_relat_1(X2))) = k1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_46]),c_0_58])).

cnf(c_0_67,plain,
    ( v1_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_52]),c_0_41])])).

cnf(c_0_68,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_40]),c_0_41])])).

fof(c_0_69,plain,(
    ! [X26,X27] :
      ( ( r1_tarski(k5_relat_1(X27,k6_relat_1(X26)),X27)
        | ~ v1_relat_1(X27) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X26),X27),X27)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

cnf(c_0_70,negated_conjecture,
    ( k6_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_33])).

fof(c_0_71,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | k5_relat_1(k6_relat_1(k1_relat_1(X30)),X30) = X30 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

cnf(c_0_72,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_73,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_41])])).

cnf(c_0_74,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_40])).

cnf(c_0_76,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( k6_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_45])).

cnf(c_0_78,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_79,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),X3)) = k5_relat_1(k6_relat_1(X1),X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_41]),c_0_41])])).

cnf(c_0_80,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_52])).

cnf(c_0_81,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_46])).

cnf(c_0_83,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))),X2) = k5_relat_1(k6_relat_1(X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_82,c_0_58])).

cnf(c_0_85,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_83]),c_0_65]),c_0_41])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:13:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.73/0.87  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.73/0.87  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.73/0.87  #
% 0.73/0.87  # Preprocessing time       : 0.027 s
% 0.73/0.87  # Presaturation interreduction done
% 0.73/0.87  
% 0.73/0.87  # Proof found!
% 0.73/0.87  # SZS status Theorem
% 0.73/0.87  # SZS output start CNFRefutation
% 0.73/0.87  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.73/0.87  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.73/0.87  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.73/0.87  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.73/0.87  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.73/0.87  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.73/0.87  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.73/0.87  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.73/0.87  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.73/0.87  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.73/0.87  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.73/0.87  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.73/0.87  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 0.73/0.87  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 0.73/0.87  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 0.73/0.87  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 0.73/0.87  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 0.73/0.87  fof(c_0_17, plain, ![X17, X18]:k1_setfam_1(k2_tarski(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.73/0.87  fof(c_0_18, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.73/0.87  fof(c_0_19, plain, ![X34, X35]:(~v1_relat_1(X35)|k1_relat_1(k7_relat_1(X35,X34))=k3_xboole_0(k1_relat_1(X35),X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.73/0.87  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.73/0.87  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.73/0.87  fof(c_0_22, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.73/0.87  fof(c_0_23, plain, ![X10, X11]:k4_xboole_0(X10,k4_xboole_0(X10,X11))=k3_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.73/0.87  fof(c_0_24, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.73/0.87  cnf(c_0_25, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.73/0.87  cnf(c_0_26, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.73/0.87  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.73/0.87  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.73/0.87  fof(c_0_29, plain, ![X20, X21]:(~v1_relat_1(X20)|v1_relat_1(k3_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.73/0.87  fof(c_0_30, plain, ![X8, X9]:r1_tarski(k3_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.73/0.87  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.73/0.87  cnf(c_0_32, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.73/0.87  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_26]), c_0_27])).
% 0.73/0.87  fof(c_0_34, plain, ![X25]:(k1_relat_1(k6_relat_1(X25))=X25&k2_relat_1(k6_relat_1(X25))=X25), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.73/0.87  fof(c_0_35, plain, ![X19]:v1_relat_1(k6_relat_1(X19)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.73/0.87  cnf(c_0_36, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.73/0.87  cnf(c_0_37, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.73/0.87  cnf(c_0_38, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_setfam_1(k2_enumset1(X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.73/0.87  cnf(c_0_39, plain, (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2))=k1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.73/0.87  cnf(c_0_40, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.73/0.87  cnf(c_0_41, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.73/0.87  cnf(c_0_42, plain, (v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_26]), c_0_27])).
% 0.73/0.87  fof(c_0_43, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.73/0.87  cnf(c_0_44, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_26]), c_0_27])).
% 0.73/0.87  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_33]), c_0_33])).
% 0.73/0.87  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.73/0.87  fof(c_0_47, plain, ![X36, X37]:(~v1_relat_1(X37)|k7_relat_1(X37,X36)=k5_relat_1(k6_relat_1(X36),X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.73/0.87  cnf(c_0_48, plain, (v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_42, c_0_33])).
% 0.73/0.87  fof(c_0_49, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).
% 0.73/0.87  cnf(c_0_50, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_44, c_0_33])).
% 0.73/0.87  cnf(c_0_51, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_46])).
% 0.73/0.87  cnf(c_0_52, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.73/0.87  cnf(c_0_53, plain, (v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_48, c_0_45])).
% 0.73/0.87  fof(c_0_54, plain, ![X28, X29]:(~v1_relat_1(X29)|(~r1_tarski(k1_relat_1(X29),X28)|k5_relat_1(k6_relat_1(X28),X29)=X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.73/0.87  cnf(c_0_55, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.73/0.87  fof(c_0_56, plain, ![X31, X32]:(~v1_relat_1(X32)|(~r1_tarski(k2_relat_1(X32),X31)|k5_relat_1(X32,k6_relat_1(X31))=X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.73/0.87  cnf(c_0_57, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)), inference(rw,[status(thm)],[c_0_50, c_0_46])).
% 0.73/0.87  cnf(c_0_58, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_41])])).
% 0.73/0.87  cnf(c_0_59, plain, (v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))|~v1_relat_1(X2)), inference(rw,[status(thm)],[c_0_53, c_0_46])).
% 0.73/0.87  cnf(c_0_60, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.73/0.87  cnf(c_0_61, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_26]), c_0_27])).
% 0.73/0.87  fof(c_0_62, plain, ![X22, X23, X24]:(~v1_relat_1(X22)|(~v1_relat_1(X23)|(~v1_relat_1(X24)|k5_relat_1(k5_relat_1(X22,X23),X24)=k5_relat_1(X22,k5_relat_1(X23,X24))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.73/0.87  cnf(c_0_63, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.73/0.87  cnf(c_0_64, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.73/0.87  cnf(c_0_65, plain, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_52]), c_0_41])])).
% 0.73/0.87  cnf(c_0_66, plain, (k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(X1)),k6_relat_1(X2)))=k1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_46]), c_0_58])).
% 0.73/0.87  cnf(c_0_67, plain, (v1_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_52]), c_0_41])])).
% 0.73/0.87  cnf(c_0_68, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_40]), c_0_41])])).
% 0.73/0.87  fof(c_0_69, plain, ![X26, X27]:((r1_tarski(k5_relat_1(X27,k6_relat_1(X26)),X27)|~v1_relat_1(X27))&(r1_tarski(k5_relat_1(k6_relat_1(X26),X27),X27)|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.73/0.87  cnf(c_0_70, negated_conjecture, (k6_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_61, c_0_33])).
% 0.73/0.87  fof(c_0_71, plain, ![X30]:(~v1_relat_1(X30)|k5_relat_1(k6_relat_1(k1_relat_1(X30)),X30)=X30), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 0.73/0.87  cnf(c_0_72, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.73/0.87  cnf(c_0_73, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_41])])).
% 0.73/0.87  cnf(c_0_74, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.73/0.87  cnf(c_0_75, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_40])).
% 0.73/0.87  cnf(c_0_76, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.73/0.87  cnf(c_0_77, negated_conjecture, (k6_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_70, c_0_45])).
% 0.73/0.87  cnf(c_0_78, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.73/0.87  cnf(c_0_79, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),X3))=k5_relat_1(k6_relat_1(X1),X3)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_41]), c_0_41])])).
% 0.73/0.87  cnf(c_0_80, plain, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)),X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_74, c_0_52])).
% 0.73/0.87  cnf(c_0_81, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.73/0.87  cnf(c_0_82, negated_conjecture, (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_77, c_0_46])).
% 0.73/0.87  cnf(c_0_83, plain, (k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))),X2)=k5_relat_1(k6_relat_1(X1),X2)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_81])).
% 0.73/0.87  cnf(c_0_84, negated_conjecture, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_82, c_0_58])).
% 0.73/0.87  cnf(c_0_85, plain, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_83]), c_0_65]), c_0_41])])).
% 0.73/0.87  cnf(c_0_86, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])]), ['proof']).
% 0.73/0.87  # SZS output end CNFRefutation
% 0.73/0.87  # Proof object total steps             : 87
% 0.73/0.87  # Proof object clause steps            : 52
% 0.73/0.87  # Proof object formula steps           : 35
% 0.73/0.87  # Proof object conjectures             : 10
% 0.73/0.87  # Proof object clause conjectures      : 7
% 0.73/0.87  # Proof object formula conjectures     : 3
% 0.73/0.87  # Proof object initial clauses used    : 18
% 0.73/0.87  # Proof object initial formulas used   : 17
% 0.73/0.87  # Proof object generating inferences   : 14
% 0.73/0.87  # Proof object simplifying inferences  : 53
% 0.73/0.87  # Training examples: 0 positive, 0 negative
% 0.73/0.87  # Parsed axioms                        : 19
% 0.73/0.87  # Removed by relevancy pruning/SinE    : 0
% 0.73/0.87  # Initial clauses                      : 23
% 0.73/0.87  # Removed in clause preprocessing      : 3
% 0.73/0.87  # Initial clauses in saturation        : 20
% 0.73/0.87  # Processed clauses                    : 1972
% 0.73/0.87  # ...of these trivial                  : 37
% 0.73/0.87  # ...subsumed                          : 1495
% 0.73/0.87  # ...remaining for further processing  : 440
% 0.73/0.87  # Other redundant clauses eliminated   : 2
% 0.73/0.87  # Clauses deleted for lack of memory   : 0
% 0.73/0.87  # Backward-subsumed                    : 22
% 0.73/0.87  # Backward-rewritten                   : 43
% 0.73/0.87  # Generated clauses                    : 38979
% 0.73/0.87  # ...of the previous two non-trivial   : 33548
% 0.73/0.87  # Contextual simplify-reflections      : 48
% 0.73/0.87  # Paramodulations                      : 38977
% 0.73/0.87  # Factorizations                       : 0
% 0.73/0.87  # Equation resolutions                 : 2
% 0.73/0.87  # Propositional unsat checks           : 0
% 0.73/0.87  #    Propositional check models        : 0
% 0.73/0.87  #    Propositional check unsatisfiable : 0
% 0.73/0.87  #    Propositional clauses             : 0
% 0.73/0.87  #    Propositional clauses after purity: 0
% 0.73/0.87  #    Propositional unsat core size     : 0
% 0.73/0.87  #    Propositional preprocessing time  : 0.000
% 0.73/0.87  #    Propositional encoding time       : 0.000
% 0.73/0.87  #    Propositional solver time         : 0.000
% 0.73/0.87  #    Success case prop preproc time    : 0.000
% 0.73/0.87  #    Success case prop encoding time   : 0.000
% 0.73/0.87  #    Success case prop solver time     : 0.000
% 0.73/0.87  # Current number of processed clauses  : 354
% 0.73/0.87  #    Positive orientable unit clauses  : 39
% 0.73/0.87  #    Positive unorientable unit clauses: 1
% 0.73/0.87  #    Negative unit clauses             : 2
% 0.73/0.87  #    Non-unit-clauses                  : 312
% 0.73/0.87  # Current number of unprocessed clauses: 31535
% 0.73/0.87  # ...number of literals in the above   : 143123
% 0.73/0.87  # Current number of archived formulas  : 0
% 0.73/0.87  # Current number of archived clauses   : 87
% 0.73/0.87  # Clause-clause subsumption calls (NU) : 22309
% 0.73/0.87  # Rec. Clause-clause subsumption calls : 14849
% 0.73/0.87  # Non-unit clause-clause subsumptions  : 1517
% 0.73/0.87  # Unit Clause-clause subsumption calls : 25
% 0.73/0.87  # Rewrite failures with RHS unbound    : 0
% 0.73/0.87  # BW rewrite match attempts            : 144
% 0.73/0.87  # BW rewrite match successes           : 73
% 0.73/0.87  # Condensation attempts                : 0
% 0.73/0.87  # Condensation successes               : 0
% 0.73/0.87  # Termbank termtop insertions          : 982535
% 0.73/0.87  
% 0.73/0.87  # -------------------------------------------------
% 0.73/0.87  # User time                : 0.513 s
% 0.73/0.87  # System time              : 0.025 s
% 0.73/0.87  # Total time               : 0.539 s
% 0.73/0.87  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
