%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:25 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  107 (1278 expanded)
%              Number of clauses        :   68 ( 605 expanded)
%              Number of leaves         :   19 ( 336 expanded)
%              Depth                    :   18
%              Number of atoms          :  174 (1762 expanded)
%              Number of equality atoms :   86 (1001 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(t192_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(c_0_19,plain,(
    ! [X18,X19] : k1_setfam_1(k2_tarski(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),X6) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_25,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k3_xboole_0(X10,X11)) = k4_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_26,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X27)
      | ~ v1_relat_1(X28)
      | ~ v1_relat_1(X29)
      | k5_relat_1(k5_relat_1(X27,X28),X29) = k5_relat_1(X27,k5_relat_1(X28,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

fof(c_0_27,plain,(
    ! [X39] :
      ( v1_relat_1(k6_relat_1(X39))
      & v1_funct_1(k6_relat_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_28,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ r1_tarski(k1_relat_1(X34),X33)
      | k5_relat_1(k6_relat_1(X33),X34) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

fof(c_0_35,plain,(
    ! [X30] :
      ( k1_relat_1(k6_relat_1(X30)) = X30
      & k2_relat_1(k6_relat_1(X30)) = X30 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_29])).

fof(c_0_39,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | v1_relat_1(k3_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_40,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k3_xboole_0(X8,X9) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_41,plain,(
    ! [X14,X15] : k2_tarski(X14,X15) = k2_tarski(X15,X14) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_42,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X1),X2),X3) = k5_relat_1(k6_relat_1(X1),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_43,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_47,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_49,plain,(
    ! [X31,X32] :
      ( ( r1_tarski(k5_relat_1(X32,k6_relat_1(X31)),X32)
        | ~ v1_relat_1(X32) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X31),X32),X32)
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

cnf(c_0_50,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3) = k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),X3))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_33])).

cnf(c_0_52,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_33])])).

cnf(c_0_53,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_54,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | k7_relat_1(X26,X25) = k7_relat_1(X26,k3_xboole_0(k1_relat_1(X26),X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).

cnf(c_0_55,plain,
    ( v1_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_47,c_0_29])).

cnf(c_0_56,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_48,c_0_29])).

cnf(c_0_57,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_23]),c_0_23])).

cnf(c_0_59,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3)) = k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_33])).

cnf(c_0_60,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(k4_xboole_0(X1,X2))) = k6_relat_1(k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_61,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | k7_relat_1(X38,X37) = k5_relat_1(k6_relat_1(X37),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_62,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_55,c_0_37])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_56,c_0_37])).

cnf(c_0_65,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_33])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_58]),c_0_37])).

cnf(c_0_67,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(k4_xboole_0(X1,X2)),k6_relat_1(X3))) = k5_relat_1(k6_relat_1(k4_xboole_0(X1,X2)),k6_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_62,c_0_29])).

cnf(c_0_70,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_46])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k6_relat_1(X1),k4_xboole_0(k6_relat_1(X1),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_72,plain,
    ( k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X2),k4_xboole_0(X1,X3))) = k7_relat_1(k6_relat_1(X2),k4_xboole_0(X1,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_33])])).

cnf(c_0_73,plain,
    ( k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2))) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_69,c_0_37])).

cnf(c_0_74,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_33])])).

cnf(c_0_75,plain,
    ( k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_44]),c_0_33])])).

cnf(c_0_76,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_33])).

fof(c_0_77,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

cnf(c_0_78,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_68]),c_0_33])])).

cnf(c_0_79,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_68]),c_0_33])])).

cnf(c_0_80,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) = k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X1),X3))
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_76]),c_0_33]),c_0_33])])).

fof(c_0_81,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_77])])])).

cnf(c_0_82,plain,
    ( r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3)),k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_78])).

cnf(c_0_83,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_33])])).

fof(c_0_84,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X24)
      | k7_relat_1(k7_relat_1(X24,X22),X23) = k7_relat_1(X24,k3_xboole_0(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_85,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

fof(c_0_86,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_87,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k1_enumset1(esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_85,c_0_29])).

cnf(c_0_90,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_91,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_68]),c_0_33])])).

cnf(c_0_92,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_88,c_0_29])).

fof(c_0_93,plain,(
    ! [X36] :
      ( ~ v1_relat_1(X36)
      | k5_relat_1(X36,k6_relat_1(k2_relat_1(X36))) = X36 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_94,negated_conjecture,
    ( k6_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_89,c_0_37])).

cnf(c_0_95,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_91])])).

cnf(c_0_96,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_92,c_0_37])).

cnf(c_0_97,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_99,negated_conjecture,
    ( k6_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_94,c_0_66])).

cnf(c_0_100,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_95]),c_0_33])])).

cnf(c_0_101,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3) = k7_relat_1(k6_relat_1(X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_76]),c_0_33])])).

cnf(c_0_102,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_33]),c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( k6_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))) != k7_relat_1(k6_relat_1(esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_104,plain,
    ( k6_relat_1(k4_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(X1),k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_100])).

cnf(c_0_105,plain,
    ( k7_relat_1(k6_relat_1(X1),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104]),c_0_105])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.53  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 0.19/0.53  # and selection function SelectNewComplexAHP.
% 0.19/0.53  #
% 0.19/0.53  # Preprocessing time       : 0.027 s
% 0.19/0.53  
% 0.19/0.53  # Proof found!
% 0.19/0.53  # SZS status Theorem
% 0.19/0.53  # SZS output start CNFRefutation
% 0.19/0.53  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.53  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.53  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.53  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.53  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.19/0.53  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 0.19/0.53  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.19/0.53  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 0.19/0.53  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.53  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.19/0.53  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.53  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.53  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 0.19/0.53  fof(t192_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 0.19/0.53  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.19/0.53  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.19/0.53  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 0.19/0.53  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.53  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 0.19/0.53  fof(c_0_19, plain, ![X18, X19]:k1_setfam_1(k2_tarski(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.53  fof(c_0_20, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.53  fof(c_0_21, plain, ![X6, X7]:r1_tarski(k3_xboole_0(X6,X7),X6), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.53  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.53  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.53  fof(c_0_24, plain, ![X12, X13]:k4_xboole_0(X12,k4_xboole_0(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.53  fof(c_0_25, plain, ![X10, X11]:k4_xboole_0(X10,k3_xboole_0(X10,X11))=k4_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.19/0.53  fof(c_0_26, plain, ![X27, X28, X29]:(~v1_relat_1(X27)|(~v1_relat_1(X28)|(~v1_relat_1(X29)|k5_relat_1(k5_relat_1(X27,X28),X29)=k5_relat_1(X27,k5_relat_1(X28,X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.19/0.53  fof(c_0_27, plain, ![X39]:(v1_relat_1(k6_relat_1(X39))&v1_funct_1(k6_relat_1(X39))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.19/0.53  cnf(c_0_28, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.53  cnf(c_0_29, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.53  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.53  cnf(c_0_31, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.53  cnf(c_0_32, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.53  cnf(c_0_33, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.53  fof(c_0_34, plain, ![X33, X34]:(~v1_relat_1(X34)|(~r1_tarski(k1_relat_1(X34),X33)|k5_relat_1(k6_relat_1(X33),X34)=X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.19/0.53  fof(c_0_35, plain, ![X30]:(k1_relat_1(k6_relat_1(X30))=X30&k2_relat_1(k6_relat_1(X30))=X30), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.53  cnf(c_0_36, plain, (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X2)),X1)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.53  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[c_0_30, c_0_29])).
% 0.19/0.53  cnf(c_0_38, plain, (k4_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_29])).
% 0.19/0.53  fof(c_0_39, plain, ![X20, X21]:(~v1_relat_1(X20)|v1_relat_1(k3_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.19/0.53  fof(c_0_40, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k3_xboole_0(X8,X9)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.53  fof(c_0_41, plain, ![X14, X15]:k2_tarski(X14,X15)=k2_tarski(X15,X14), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.53  cnf(c_0_42, plain, (k5_relat_1(k5_relat_1(k6_relat_1(X1),X2),X3)=k5_relat_1(k6_relat_1(X1),k5_relat_1(X2,X3))|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.53  cnf(c_0_43, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.53  cnf(c_0_44, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.53  cnf(c_0_45, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.53  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_38, c_0_37])).
% 0.19/0.53  cnf(c_0_47, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.53  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.53  fof(c_0_49, plain, ![X31, X32]:((r1_tarski(k5_relat_1(X32,k6_relat_1(X31)),X32)|~v1_relat_1(X32))&(r1_tarski(k5_relat_1(k6_relat_1(X31),X32),X32)|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.19/0.53  cnf(c_0_50, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.53  cnf(c_0_51, plain, (k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3)=k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),X3))|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_42, c_0_33])).
% 0.19/0.53  cnf(c_0_52, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_33])])).
% 0.19/0.53  cnf(c_0_53, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.53  fof(c_0_54, plain, ![X25, X26]:(~v1_relat_1(X26)|k7_relat_1(X26,X25)=k7_relat_1(X26,k3_xboole_0(k1_relat_1(X26),X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).
% 0.19/0.53  cnf(c_0_55, plain, (v1_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_47, c_0_29])).
% 0.19/0.53  cnf(c_0_56, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_48, c_0_29])).
% 0.19/0.53  cnf(c_0_57, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.53  cnf(c_0_58, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_23]), c_0_23])).
% 0.19/0.53  cnf(c_0_59, plain, (k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3))=k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))), inference(spm,[status(thm)],[c_0_51, c_0_33])).
% 0.19/0.53  cnf(c_0_60, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(k4_xboole_0(X1,X2)))=k6_relat_1(k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.53  fof(c_0_61, plain, ![X37, X38]:(~v1_relat_1(X38)|k7_relat_1(X38,X37)=k5_relat_1(k6_relat_1(X37),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.19/0.53  cnf(c_0_62, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.53  cnf(c_0_63, plain, (v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_55, c_0_37])).
% 0.19/0.53  cnf(c_0_64, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_56, c_0_37])).
% 0.19/0.53  cnf(c_0_65, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_57, c_0_33])).
% 0.19/0.53  cnf(c_0_66, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_58]), c_0_37])).
% 0.19/0.53  cnf(c_0_67, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(k4_xboole_0(X1,X2)),k6_relat_1(X3)))=k5_relat_1(k6_relat_1(k4_xboole_0(X1,X2)),k6_relat_1(X3))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.53  cnf(c_0_68, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.53  cnf(c_0_69, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_62, c_0_29])).
% 0.19/0.53  cnf(c_0_70, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_63, c_0_46])).
% 0.19/0.53  cnf(c_0_71, plain, (k4_xboole_0(k6_relat_1(X1),k4_xboole_0(k6_relat_1(X1),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.19/0.53  cnf(c_0_72, plain, (k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X2),k4_xboole_0(X1,X3)))=k7_relat_1(k6_relat_1(X2),k4_xboole_0(X1,X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_33])])).
% 0.19/0.53  cnf(c_0_73, plain, (k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2)))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_69, c_0_37])).
% 0.19/0.53  cnf(c_0_74, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_33])])).
% 0.19/0.53  cnf(c_0_75, plain, (k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_44]), c_0_33])])).
% 0.19/0.53  cnf(c_0_76, plain, (k7_relat_1(k6_relat_1(X1),X2)=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_68, c_0_33])).
% 0.19/0.53  fof(c_0_77, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.19/0.53  cnf(c_0_78, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_68]), c_0_33])])).
% 0.19/0.53  cnf(c_0_79, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_68]), c_0_33])])).
% 0.19/0.53  cnf(c_0_80, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)=k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X1),X3))|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_76]), c_0_33]), c_0_33])])).
% 0.19/0.53  fof(c_0_81, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_77])])])).
% 0.19/0.53  cnf(c_0_82, plain, (r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3)),k7_relat_1(k6_relat_1(X1),X2))), inference(spm,[status(thm)],[c_0_57, c_0_78])).
% 0.19/0.53  cnf(c_0_83, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_33])])).
% 0.19/0.53  fof(c_0_84, plain, ![X22, X23, X24]:(~v1_relat_1(X24)|k7_relat_1(k7_relat_1(X24,X22),X23)=k7_relat_1(X24,k3_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.19/0.53  cnf(c_0_85, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.19/0.53  fof(c_0_86, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.53  cnf(c_0_87, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k7_relat_1(k6_relat_1(X1),X2))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.53  cnf(c_0_88, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.19/0.53  cnf(c_0_89, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k1_enumset1(esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[c_0_85, c_0_29])).
% 0.19/0.53  cnf(c_0_90, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.19/0.53  cnf(c_0_91, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k7_relat_1(k6_relat_1(X2),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_68]), c_0_33])])).
% 0.19/0.53  cnf(c_0_92, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_88, c_0_29])).
% 0.19/0.53  fof(c_0_93, plain, ![X36]:(~v1_relat_1(X36)|k5_relat_1(X36,k6_relat_1(k2_relat_1(X36)))=X36), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.19/0.53  cnf(c_0_94, negated_conjecture, (k6_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_89, c_0_37])).
% 0.19/0.53  cnf(c_0_95, plain, (k7_relat_1(k6_relat_1(X1),X2)=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_91])])).
% 0.19/0.53  cnf(c_0_96, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_92, c_0_37])).
% 0.19/0.53  cnf(c_0_97, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.19/0.53  cnf(c_0_98, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.53  cnf(c_0_99, negated_conjecture, (k6_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_94, c_0_66])).
% 0.19/0.53  cnf(c_0_100, plain, (k7_relat_1(k6_relat_1(X1),X2)=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_95]), c_0_33])])).
% 0.19/0.53  cnf(c_0_101, plain, (k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3)=k7_relat_1(k6_relat_1(X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_76]), c_0_33])])).
% 0.19/0.53  cnf(c_0_102, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_33]), c_0_98])).
% 0.19/0.53  cnf(c_0_103, negated_conjecture, (k6_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)))!=k7_relat_1(k6_relat_1(esk2_0),esk1_0)), inference(rw,[status(thm)],[c_0_99, c_0_100])).
% 0.19/0.53  cnf(c_0_104, plain, (k6_relat_1(k4_xboole_0(X1,X2))=k7_relat_1(k6_relat_1(X1),k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_60, c_0_100])).
% 0.19/0.53  cnf(c_0_105, plain, (k7_relat_1(k6_relat_1(X1),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.19/0.53  cnf(c_0_106, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104]), c_0_105])]), ['proof']).
% 0.19/0.53  # SZS output end CNFRefutation
% 0.19/0.53  # Proof object total steps             : 107
% 0.19/0.53  # Proof object clause steps            : 68
% 0.19/0.53  # Proof object formula steps           : 39
% 0.19/0.53  # Proof object conjectures             : 9
% 0.19/0.53  # Proof object clause conjectures      : 6
% 0.19/0.53  # Proof object formula conjectures     : 3
% 0.19/0.53  # Proof object initial clauses used    : 20
% 0.19/0.53  # Proof object initial formulas used   : 19
% 0.19/0.53  # Proof object generating inferences   : 27
% 0.19/0.53  # Proof object simplifying inferences  : 53
% 0.19/0.53  # Training examples: 0 positive, 0 negative
% 0.19/0.53  # Parsed axioms                        : 20
% 0.19/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.53  # Initial clauses                      : 25
% 0.19/0.53  # Removed in clause preprocessing      : 2
% 0.19/0.53  # Initial clauses in saturation        : 23
% 0.19/0.53  # Processed clauses                    : 1178
% 0.19/0.53  # ...of these trivial                  : 259
% 0.19/0.53  # ...subsumed                          : 561
% 0.19/0.53  # ...remaining for further processing  : 358
% 0.19/0.53  # Other redundant clauses eliminated   : 2
% 0.19/0.53  # Clauses deleted for lack of memory   : 0
% 0.19/0.53  # Backward-subsumed                    : 12
% 0.19/0.53  # Backward-rewritten                   : 81
% 0.19/0.53  # Generated clauses                    : 15236
% 0.19/0.53  # ...of the previous two non-trivial   : 11555
% 0.19/0.53  # Contextual simplify-reflections      : 0
% 0.19/0.53  # Paramodulations                      : 15234
% 0.19/0.53  # Factorizations                       : 0
% 0.19/0.53  # Equation resolutions                 : 2
% 0.19/0.53  # Propositional unsat checks           : 0
% 0.19/0.53  #    Propositional check models        : 0
% 0.19/0.53  #    Propositional check unsatisfiable : 0
% 0.19/0.53  #    Propositional clauses             : 0
% 0.19/0.53  #    Propositional clauses after purity: 0
% 0.19/0.53  #    Propositional unsat core size     : 0
% 0.19/0.53  #    Propositional preprocessing time  : 0.000
% 0.19/0.53  #    Propositional encoding time       : 0.000
% 0.19/0.53  #    Propositional solver time         : 0.000
% 0.19/0.53  #    Success case prop preproc time    : 0.000
% 0.19/0.53  #    Success case prop encoding time   : 0.000
% 0.19/0.53  #    Success case prop solver time     : 0.000
% 0.19/0.53  # Current number of processed clauses  : 263
% 0.19/0.53  #    Positive orientable unit clauses  : 116
% 0.19/0.53  #    Positive unorientable unit clauses: 6
% 0.19/0.53  #    Negative unit clauses             : 0
% 0.19/0.53  #    Non-unit-clauses                  : 141
% 0.19/0.53  # Current number of unprocessed clauses: 10339
% 0.19/0.53  # ...number of literals in the above   : 21703
% 0.19/0.53  # Current number of archived formulas  : 0
% 0.19/0.53  # Current number of archived clauses   : 95
% 0.19/0.53  # Clause-clause subsumption calls (NU) : 3457
% 0.19/0.53  # Rec. Clause-clause subsumption calls : 3250
% 0.19/0.53  # Non-unit clause-clause subsumptions  : 565
% 0.19/0.53  # Unit Clause-clause subsumption calls : 133
% 0.19/0.53  # Rewrite failures with RHS unbound    : 0
% 0.19/0.53  # BW rewrite match attempts            : 824
% 0.19/0.53  # BW rewrite match successes           : 118
% 0.19/0.53  # Condensation attempts                : 0
% 0.19/0.53  # Condensation successes               : 0
% 0.19/0.53  # Termbank termtop insertions          : 261682
% 0.19/0.53  
% 0.19/0.53  # -------------------------------------------------
% 0.19/0.53  # User time                : 0.180 s
% 0.19/0.53  # System time              : 0.011 s
% 0.19/0.53  # Total time               : 0.191 s
% 0.19/0.53  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
