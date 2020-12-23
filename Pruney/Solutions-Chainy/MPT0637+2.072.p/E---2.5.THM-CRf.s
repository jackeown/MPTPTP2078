%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:34 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  133 (4315 expanded)
%              Number of clauses        :   88 (1848 expanded)
%              Number of leaves         :   22 (1233 expanded)
%              Depth                    :   19
%              Number of atoms          :  250 (9386 expanded)
%              Number of equality atoms :  102 (2521 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc24_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v4_relat_1(k6_relat_1(X1),X1)
      & v5_relat_1(k6_relat_1(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(t72_relat_1,axiom,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t103_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(t140_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k8_relat_1(X1,X3),X2) = k8_relat_1(X1,k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(c_0_22,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r1_tarski(k2_relat_1(X33),X32)
      | k8_relat_1(X32,X33) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

fof(c_0_23,plain,(
    ! [X43] :
      ( k1_relat_1(k6_relat_1(X43)) = X43
      & k2_relat_1(k6_relat_1(X43)) = X43 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_24,plain,(
    ! [X52] :
      ( v1_relat_1(k6_relat_1(X52))
      & v4_relat_1(k6_relat_1(X52),X52)
      & v5_relat_1(k6_relat_1(X52),X52) ) ),
    inference(variable_rename,[status(thm)],[fc24_relat_1])).

fof(c_0_25,plain,(
    ! [X41,X42] :
      ( ~ v1_relat_1(X41)
      | ~ v1_relat_1(X42)
      | k4_relat_1(k5_relat_1(X41,X42)) = k5_relat_1(k4_relat_1(X42),k4_relat_1(X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_26,plain,(
    ! [X44] : k4_relat_1(k6_relat_1(X44)) = k6_relat_1(X44) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

fof(c_0_27,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | k8_relat_1(X30,X31) = k5_relat_1(X31,k6_relat_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

cnf(c_0_28,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X45,X46] :
      ( ( r1_tarski(k5_relat_1(X46,k6_relat_1(X45)),X46)
        | ~ v1_relat_1(X46) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X45),X46),X46)
        | ~ v1_relat_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

fof(c_0_32,plain,(
    ! [X49,X50] :
      ( ~ v1_relat_1(X50)
      | k7_relat_1(X50,X49) = k5_relat_1(k6_relat_1(X49),X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_33,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ v1_relat_1(X23)
      | v1_relat_1(k5_relat_1(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_34,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_38,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ r1_tarski(X27,X28)
      | k7_relat_1(k7_relat_1(X29,X28),X27) = k7_relat_1(X29,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).

cnf(c_0_41,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X1))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_30])])).

cnf(c_0_43,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_30])])).

cnf(c_0_44,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( k7_relat_1(k7_relat_1(X1,X3),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_39]),c_0_30])])).

fof(c_0_47,plain,(
    ! [X51] :
      ( ~ v1_relat_1(X51)
      | k7_relat_1(X51,k1_relat_1(X51)) = X51 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

fof(c_0_48,plain,(
    ! [X39,X40] :
      ( ( r1_tarski(k1_relat_1(X39),k1_relat_1(X40))
        | ~ r1_tarski(X39,X40)
        | ~ v1_relat_1(X40)
        | ~ v1_relat_1(X39) )
      & ( r1_tarski(k2_relat_1(X39),k2_relat_1(X40))
        | ~ r1_tarski(X39,X40)
        | ~ v1_relat_1(X40)
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_49,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | ~ v4_relat_1(X38,X37)
      | X38 = k7_relat_1(X38,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_50,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35]),c_0_35]),c_0_30])])).

cnf(c_0_51,plain,
    ( r1_tarski(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ r1_tarski(X2,X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_52,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_55,plain,(
    ! [X20,X21] : k1_setfam_1(k2_tarski(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_56,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_57,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(X48)
      | r1_tarski(k1_relat_1(k7_relat_1(X48,X47)),X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_58,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( v4_relat_1(k6_relat_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_60,plain,
    ( k6_relat_1(X1) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_50])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k7_relat_1(X1,X2))
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_30])])).

cnf(c_0_63,plain,
    ( k5_relat_1(k4_relat_1(X1),k6_relat_1(X2)) = k4_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_39])).

cnf(c_0_64,plain,
    ( k4_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_30])])).

fof(c_0_65,plain,(
    ! [X34,X35,X36] :
      ( ~ v1_relat_1(X36)
      | k7_relat_1(k8_relat_1(X34,X36),X35) = k8_relat_1(X34,k7_relat_1(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).

fof(c_0_66,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | k7_relat_1(k7_relat_1(X26,X24),X25) = k7_relat_1(X26,k3_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_67,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_69,plain,(
    ! [X8,X9,X10] : k2_enumset1(X8,X8,X9,X10) = k1_enumset1(X8,X9,X10) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_70,plain,(
    ! [X11,X12,X13,X14] : k3_enumset1(X11,X11,X12,X13,X14) = k2_enumset1(X11,X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_71,plain,(
    ! [X15,X16,X17,X18,X19] : k4_enumset1(X15,X15,X16,X17,X18,X19) = k3_enumset1(X15,X16,X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_73,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_30])])).

cnf(c_0_74,plain,
    ( k6_relat_1(k7_relat_1(X1,X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_44])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,k7_relat_1(X1,X2))
    | ~ r1_tarski(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_76,plain,
    ( v1_relat_1(k4_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_63]),c_0_30])])).

cnf(c_0_77,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_39]),c_0_35]),c_0_30]),c_0_30])])).

cnf(c_0_78,plain,
    ( k7_relat_1(k8_relat_1(X2,X1),X3) = k8_relat_1(X2,k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_79,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_80,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_81,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_82,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_83,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_54]),c_0_30])])).

cnf(c_0_85,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_86,plain,
    ( k6_relat_1(k7_relat_1(X1,X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_87,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_35]),c_0_30]),c_0_30])])).

cnf(c_0_88,plain,
    ( k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X2) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_73]),c_0_30])])).

cnf(c_0_89,plain,
    ( k7_relat_1(k8_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(X1))
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_78]),c_0_46])).

cnf(c_0_90,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_82]),c_0_83])).

cnf(c_0_91,plain,
    ( k8_relat_1(k2_relat_1(X1),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_84])).

cnf(c_0_92,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_29]),c_0_30])])).

cnf(c_0_93,plain,
    ( k6_relat_1(k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X2)) = k6_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_38]),c_0_87]),c_0_30])])).

cnf(c_0_94,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_73]),c_0_30])])).

cnf(c_0_95,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_90])).

cnf(c_0_96,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_43]),c_0_30])])).

cnf(c_0_97,plain,
    ( k8_relat_1(X1,k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_29]),c_0_30])])).

cnf(c_0_98,plain,
    ( k8_relat_1(X1,X2) = X2
    | ~ r1_tarski(X2,k6_relat_1(X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_92])).

cnf(c_0_99,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X2) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_93]),c_0_29])).

cnf(c_0_100,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X3),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_94]),c_0_30])])).

cnf(c_0_101,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_102,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_73]),c_0_30])])).

cnf(c_0_103,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3) = k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))
    | ~ r1_tarski(X3,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_96]),c_0_30])]),c_0_94]),c_0_94])).

cnf(c_0_104,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_97]),c_0_30])])).

cnf(c_0_105,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ r1_tarski(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_98])).

cnf(c_0_106,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_107,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_39]),c_0_30]),c_0_30])])).

cnf(c_0_108,plain,
    ( k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)) = k6_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_44]),c_0_102]),c_0_30])])).

cnf(c_0_109,plain,
    ( k6_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k6_relat_1(k6_relat_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_103]),c_0_104])).

cnf(c_0_110,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_107]),c_0_102])])).

cnf(c_0_111,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_108]),c_0_29])).

cnf(c_0_112,plain,
    ( k6_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k6_relat_1(k6_relat_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_113,plain,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_45]),c_0_46]),c_0_72])).

cnf(c_0_114,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_111]),c_0_102])])).

fof(c_0_115,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

cnf(c_0_116,plain,
    ( k6_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))) = k6_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114]),c_0_30])])).

cnf(c_0_117,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_110]),c_0_77]),c_0_110]),c_0_35]),c_0_110]),c_0_30])])).

fof(c_0_118,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_115])])])).

cnf(c_0_119,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X1),X2) = k6_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_90]),c_0_30])])).

cnf(c_0_120,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[c_0_94,c_0_110])).

cnf(c_0_121,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_116]),c_0_29])).

cnf(c_0_122,plain,
    ( k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_117]),c_0_94]),c_0_110]),c_0_30])])).

cnf(c_0_123,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_124,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X2) = k6_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_119,c_0_117])).

cnf(c_0_125,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_122])).

cnf(c_0_126,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_94]),c_0_94])).

cnf(c_0_127,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_80]),c_0_81]),c_0_82]),c_0_83])).

cnf(c_0_128,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))) = k6_relat_1(k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_129,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X2) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_39]),c_0_30])])).

cnf(c_0_130,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))) != k7_relat_1(k6_relat_1(esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_127,c_0_110])).

cnf(c_0_131,plain,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_128]),c_0_129]),c_0_111]),c_0_102])])).

cnf(c_0_132,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_131])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 2.85/3.08  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.85/3.08  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.85/3.08  #
% 2.85/3.08  # Preprocessing time       : 0.027 s
% 2.85/3.08  # Presaturation interreduction done
% 2.85/3.08  
% 2.85/3.08  # Proof found!
% 2.85/3.08  # SZS status Theorem
% 2.85/3.08  # SZS output start CNFRefutation
% 2.85/3.08  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.85/3.08  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.85/3.08  fof(fc24_relat_1, axiom, ![X1]:((v1_relat_1(k6_relat_1(X1))&v4_relat_1(k6_relat_1(X1),X1))&v5_relat_1(k6_relat_1(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.85/3.08  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 2.85/3.08  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 2.85/3.08  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.85/3.08  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 2.85/3.08  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.85/3.08  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.85/3.08  fof(t103_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 2.85/3.08  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.85/3.08  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.85/3.08  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.85/3.08  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.85/3.08  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.85/3.08  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.85/3.08  fof(t140_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k8_relat_1(X1,X3),X2)=k8_relat_1(X1,k7_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 2.85/3.08  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.85/3.08  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.85/3.08  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.85/3.08  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.85/3.08  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.85/3.08  fof(c_0_22, plain, ![X32, X33]:(~v1_relat_1(X33)|(~r1_tarski(k2_relat_1(X33),X32)|k8_relat_1(X32,X33)=X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 2.85/3.08  fof(c_0_23, plain, ![X43]:(k1_relat_1(k6_relat_1(X43))=X43&k2_relat_1(k6_relat_1(X43))=X43), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 2.85/3.08  fof(c_0_24, plain, ![X52]:((v1_relat_1(k6_relat_1(X52))&v4_relat_1(k6_relat_1(X52),X52))&v5_relat_1(k6_relat_1(X52),X52)), inference(variable_rename,[status(thm)],[fc24_relat_1])).
% 2.85/3.08  fof(c_0_25, plain, ![X41, X42]:(~v1_relat_1(X41)|(~v1_relat_1(X42)|k4_relat_1(k5_relat_1(X41,X42))=k5_relat_1(k4_relat_1(X42),k4_relat_1(X41)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 2.85/3.08  fof(c_0_26, plain, ![X44]:k4_relat_1(k6_relat_1(X44))=k6_relat_1(X44), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 2.85/3.08  fof(c_0_27, plain, ![X30, X31]:(~v1_relat_1(X31)|k8_relat_1(X30,X31)=k5_relat_1(X31,k6_relat_1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 2.85/3.08  cnf(c_0_28, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.85/3.08  cnf(c_0_29, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.85/3.08  cnf(c_0_30, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.85/3.08  fof(c_0_31, plain, ![X45, X46]:((r1_tarski(k5_relat_1(X46,k6_relat_1(X45)),X46)|~v1_relat_1(X46))&(r1_tarski(k5_relat_1(k6_relat_1(X45),X46),X46)|~v1_relat_1(X46))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 2.85/3.08  fof(c_0_32, plain, ![X49, X50]:(~v1_relat_1(X50)|k7_relat_1(X50,X49)=k5_relat_1(k6_relat_1(X49),X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 2.85/3.08  fof(c_0_33, plain, ![X22, X23]:(~v1_relat_1(X22)|~v1_relat_1(X23)|v1_relat_1(k5_relat_1(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 2.85/3.08  cnf(c_0_34, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.85/3.08  cnf(c_0_35, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.85/3.08  cnf(c_0_36, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.85/3.08  cnf(c_0_37, plain, (k8_relat_1(X1,k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 2.85/3.08  cnf(c_0_38, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.85/3.08  cnf(c_0_39, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.85/3.08  fof(c_0_40, plain, ![X27, X28, X29]:(~v1_relat_1(X29)|(~r1_tarski(X27,X28)|k7_relat_1(k7_relat_1(X29,X28),X27)=k7_relat_1(X29,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).
% 2.85/3.08  cnf(c_0_41, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.85/3.08  cnf(c_0_42, plain, (k4_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k4_relat_1(X2),k6_relat_1(X1))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_30])])).
% 2.85/3.08  cnf(c_0_43, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_30])])).
% 2.85/3.08  cnf(c_0_44, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 2.85/3.08  cnf(c_0_45, plain, (k7_relat_1(k7_relat_1(X1,X3),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.85/3.08  cnf(c_0_46, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_39]), c_0_30])])).
% 2.85/3.08  fof(c_0_47, plain, ![X51]:(~v1_relat_1(X51)|k7_relat_1(X51,k1_relat_1(X51))=X51), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 2.85/3.08  fof(c_0_48, plain, ![X39, X40]:((r1_tarski(k1_relat_1(X39),k1_relat_1(X40))|~r1_tarski(X39,X40)|~v1_relat_1(X40)|~v1_relat_1(X39))&(r1_tarski(k2_relat_1(X39),k2_relat_1(X40))|~r1_tarski(X39,X40)|~v1_relat_1(X40)|~v1_relat_1(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 2.85/3.08  fof(c_0_49, plain, ![X37, X38]:(~v1_relat_1(X38)|~v4_relat_1(X38,X37)|X38=k7_relat_1(X38,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 2.85/3.08  cnf(c_0_50, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_35]), c_0_35]), c_0_30])])).
% 2.85/3.08  cnf(c_0_51, plain, (r1_tarski(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~r1_tarski(X2,X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 2.85/3.08  cnf(c_0_52, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.85/3.08  cnf(c_0_53, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 2.85/3.08  cnf(c_0_54, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.85/3.08  fof(c_0_55, plain, ![X20, X21]:k1_setfam_1(k2_tarski(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 2.85/3.08  fof(c_0_56, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.85/3.08  fof(c_0_57, plain, ![X47, X48]:(~v1_relat_1(X48)|r1_tarski(k1_relat_1(k7_relat_1(X48,X47)),X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 2.85/3.08  cnf(c_0_58, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 2.85/3.08  cnf(c_0_59, plain, (v4_relat_1(k6_relat_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.85/3.08  cnf(c_0_60, plain, (k6_relat_1(X1)=k6_relat_1(X2)|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_43, c_0_50])).
% 2.85/3.08  cnf(c_0_61, plain, (r1_tarski(X1,k7_relat_1(X1,X2))|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 2.85/3.08  cnf(c_0_62, plain, (r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_30])])).
% 2.85/3.08  cnf(c_0_63, plain, (k5_relat_1(k4_relat_1(X1),k6_relat_1(X2))=k4_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_39])).
% 2.85/3.08  cnf(c_0_64, plain, (k4_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k5_relat_1(k6_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_30])])).
% 2.85/3.08  fof(c_0_65, plain, ![X34, X35, X36]:(~v1_relat_1(X36)|k7_relat_1(k8_relat_1(X34,X36),X35)=k8_relat_1(X34,k7_relat_1(X36,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).
% 2.85/3.08  fof(c_0_66, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|k7_relat_1(k7_relat_1(X26,X24),X25)=k7_relat_1(X26,k3_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 2.85/3.08  cnf(c_0_67, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 2.85/3.08  cnf(c_0_68, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 2.85/3.08  fof(c_0_69, plain, ![X8, X9, X10]:k2_enumset1(X8,X8,X9,X10)=k1_enumset1(X8,X9,X10), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 2.85/3.08  fof(c_0_70, plain, ![X11, X12, X13, X14]:k3_enumset1(X11,X11,X12,X13,X14)=k2_enumset1(X11,X12,X13,X14), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 2.85/3.08  fof(c_0_71, plain, ![X15, X16, X17, X18, X19]:k4_enumset1(X15,X15,X16,X17,X18,X19)=k3_enumset1(X15,X16,X17,X18,X19), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 2.85/3.08  cnf(c_0_72, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 2.85/3.08  cnf(c_0_73, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_30])])).
% 2.85/3.08  cnf(c_0_74, plain, (k6_relat_1(k7_relat_1(X1,X2))=k6_relat_1(X1)|~r1_tarski(X1,k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_60, c_0_44])).
% 2.85/3.08  cnf(c_0_75, plain, (r1_tarski(X1,k7_relat_1(X1,X2))|~r1_tarski(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 2.85/3.08  cnf(c_0_76, plain, (v1_relat_1(k4_relat_1(k7_relat_1(X1,X2)))|~v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_63]), c_0_30])])).
% 2.85/3.08  cnf(c_0_77, plain, (k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_39]), c_0_35]), c_0_30]), c_0_30])])).
% 2.85/3.08  cnf(c_0_78, plain, (k7_relat_1(k8_relat_1(X2,X1),X3)=k8_relat_1(X2,k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 2.85/3.08  cnf(c_0_79, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 2.85/3.08  cnf(c_0_80, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 2.85/3.08  cnf(c_0_81, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 2.85/3.08  cnf(c_0_82, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 2.85/3.08  cnf(c_0_83, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 2.85/3.08  cnf(c_0_84, plain, (r1_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_54]), c_0_30])])).
% 2.85/3.08  cnf(c_0_85, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 2.85/3.08  cnf(c_0_86, plain, (k6_relat_1(k7_relat_1(X1,X2))=k6_relat_1(X1)|~r1_tarski(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 2.85/3.08  cnf(c_0_87, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_35]), c_0_30]), c_0_30])])).
% 2.85/3.08  cnf(c_0_88, plain, (k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X2)=k8_relat_1(X1,k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_73]), c_0_30])])).
% 2.85/3.08  cnf(c_0_89, plain, (k7_relat_1(k8_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(X1))|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_78]), c_0_46])).
% 2.85/3.08  cnf(c_0_90, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80]), c_0_81]), c_0_82]), c_0_83])).
% 2.85/3.08  cnf(c_0_91, plain, (k8_relat_1(k2_relat_1(X1),X1)=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_84])).
% 2.85/3.08  cnf(c_0_92, plain, (r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_29]), c_0_30])])).
% 2.85/3.08  cnf(c_0_93, plain, (k6_relat_1(k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X2))=k6_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_38]), c_0_87]), c_0_30])])).
% 2.85/3.08  cnf(c_0_94, plain, (k8_relat_1(X1,k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_73]), c_0_30])])).
% 2.85/3.08  cnf(c_0_95, plain, (v1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_90])).
% 2.85/3.08  cnf(c_0_96, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_43]), c_0_30])])).
% 2.85/3.08  cnf(c_0_97, plain, (k8_relat_1(X1,k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_29]), c_0_30])])).
% 2.85/3.08  cnf(c_0_98, plain, (k8_relat_1(X1,X2)=X2|~r1_tarski(X2,k6_relat_1(X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_28, c_0_92])).
% 2.85/3.08  cnf(c_0_99, plain, (k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X2)=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_93]), c_0_29])).
% 2.85/3.08  cnf(c_0_100, plain, (k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3)=k5_relat_1(k7_relat_1(k6_relat_1(X1),X3),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_94]), c_0_30])])).
% 2.85/3.08  cnf(c_0_101, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.85/3.08  cnf(c_0_102, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_73]), c_0_30])])).
% 2.85/3.08  cnf(c_0_103, plain, (k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3)=k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))|~r1_tarski(X3,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_96]), c_0_30])]), c_0_94]), c_0_94])).
% 2.85/3.08  cnf(c_0_104, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_97]), c_0_30])])).
% 2.85/3.08  cnf(c_0_105, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~r1_tarski(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_98])).
% 2.85/3.08  cnf(c_0_106, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_99, c_0_100])).
% 2.85/3.08  cnf(c_0_107, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_39]), c_0_30]), c_0_30])])).
% 2.85/3.08  cnf(c_0_108, plain, (k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1))=k6_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_44]), c_0_102]), c_0_30])])).
% 2.85/3.08  cnf(c_0_109, plain, (k6_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k6_relat_1(k6_relat_1(X2))|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_103]), c_0_104])).
% 2.85/3.08  cnf(c_0_110, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_107]), c_0_102])])).
% 2.85/3.08  cnf(c_0_111, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_108]), c_0_29])).
% 2.85/3.08  cnf(c_0_112, plain, (k6_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k6_relat_1(k6_relat_1(X2))|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[c_0_109, c_0_110])).
% 2.85/3.08  cnf(c_0_113, plain, (k7_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2)))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_45]), c_0_46]), c_0_72])).
% 2.85/3.08  cnf(c_0_114, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_111]), c_0_102])])).
% 2.85/3.08  fof(c_0_115, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 2.85/3.08  cnf(c_0_116, plain, (k6_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))))=k6_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_114]), c_0_30])])).
% 2.85/3.08  cnf(c_0_117, plain, (k7_relat_1(k6_relat_1(X1),X2)=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_110]), c_0_77]), c_0_110]), c_0_35]), c_0_110]), c_0_30])])).
% 2.85/3.08  fof(c_0_118, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_115])])])).
% 2.85/3.08  cnf(c_0_119, plain, (k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X1),X2)=k6_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_90]), c_0_30])])).
% 2.85/3.08  cnf(c_0_120, plain, (k8_relat_1(X1,k6_relat_1(X2))=k7_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[c_0_94, c_0_110])).
% 2.85/3.08  cnf(c_0_121, plain, (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_116]), c_0_29])).
% 2.85/3.08  cnf(c_0_122, plain, (k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3))=k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_117]), c_0_94]), c_0_110]), c_0_30])])).
% 2.85/3.08  cnf(c_0_123, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_118])).
% 2.85/3.08  cnf(c_0_124, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X2)=k6_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[c_0_119, c_0_117])).
% 2.85/3.08  cnf(c_0_125, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)=k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_122])).
% 2.85/3.08  cnf(c_0_126, plain, (k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X1)=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_94]), c_0_94])).
% 2.85/3.08  cnf(c_0_127, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_80]), c_0_81]), c_0_82]), c_0_83])).
% 2.85/3.08  cnf(c_0_128, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1)))=k6_relat_1(k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1)))), inference(rw,[status(thm)],[c_0_124, c_0_125])).
% 2.85/3.08  cnf(c_0_129, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X2)=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_39]), c_0_30])])).
% 2.85/3.08  cnf(c_0_130, negated_conjecture, (k6_relat_1(k1_setfam_1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))!=k7_relat_1(k6_relat_1(esk2_0),esk1_0)), inference(rw,[status(thm)],[c_0_127, c_0_110])).
% 2.85/3.08  cnf(c_0_131, plain, (k6_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_128]), c_0_129]), c_0_111]), c_0_102])])).
% 2.85/3.08  cnf(c_0_132, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_131])]), ['proof']).
% 2.85/3.08  # SZS output end CNFRefutation
% 2.85/3.08  # Proof object total steps             : 133
% 2.85/3.08  # Proof object clause steps            : 88
% 2.85/3.08  # Proof object formula steps           : 45
% 2.85/3.08  # Proof object conjectures             : 7
% 2.85/3.08  # Proof object clause conjectures      : 4
% 2.85/3.08  # Proof object formula conjectures     : 3
% 2.85/3.08  # Proof object initial clauses used    : 26
% 2.85/3.08  # Proof object initial formulas used   : 22
% 2.85/3.08  # Proof object generating inferences   : 51
% 2.85/3.08  # Proof object simplifying inferences  : 115
% 2.85/3.08  # Training examples: 0 positive, 0 negative
% 2.85/3.08  # Parsed axioms                        : 22
% 2.85/3.08  # Removed by relevancy pruning/SinE    : 0
% 2.85/3.08  # Initial clauses                      : 27
% 2.85/3.08  # Removed in clause preprocessing      : 5
% 2.85/3.08  # Initial clauses in saturation        : 22
% 2.85/3.08  # Processed clauses                    : 11749
% 2.85/3.08  # ...of these trivial                  : 273
% 2.85/3.08  # ...subsumed                          : 9833
% 2.85/3.08  # ...remaining for further processing  : 1643
% 2.85/3.08  # Other redundant clauses eliminated   : 0
% 2.85/3.08  # Clauses deleted for lack of memory   : 0
% 2.85/3.08  # Backward-subsumed                    : 22
% 2.85/3.08  # Backward-rewritten                   : 86
% 2.85/3.08  # Generated clauses                    : 350738
% 2.85/3.08  # ...of the previous two non-trivial   : 323567
% 2.85/3.08  # Contextual simplify-reflections      : 166
% 2.85/3.08  # Paramodulations                      : 350738
% 2.85/3.08  # Factorizations                       : 0
% 2.85/3.08  # Equation resolutions                 : 0
% 2.85/3.08  # Propositional unsat checks           : 0
% 2.85/3.08  #    Propositional check models        : 0
% 2.85/3.08  #    Propositional check unsatisfiable : 0
% 2.85/3.08  #    Propositional clauses             : 0
% 2.85/3.08  #    Propositional clauses after purity: 0
% 2.85/3.08  #    Propositional unsat core size     : 0
% 2.85/3.08  #    Propositional preprocessing time  : 0.000
% 2.85/3.08  #    Propositional encoding time       : 0.000
% 2.85/3.08  #    Propositional solver time         : 0.000
% 2.85/3.08  #    Success case prop preproc time    : 0.000
% 2.85/3.08  #    Success case prop encoding time   : 0.000
% 2.85/3.08  #    Success case prop solver time     : 0.000
% 2.85/3.08  # Current number of processed clauses  : 1513
% 2.85/3.08  #    Positive orientable unit clauses  : 94
% 2.85/3.08  #    Positive unorientable unit clauses: 2
% 2.85/3.08  #    Negative unit clauses             : 0
% 2.85/3.08  #    Non-unit-clauses                  : 1417
% 2.85/3.08  # Current number of unprocessed clauses: 311036
% 2.85/3.08  # ...number of literals in the above   : 1160369
% 2.85/3.08  # Current number of archived formulas  : 0
% 2.85/3.08  # Current number of archived clauses   : 135
% 2.85/3.08  # Clause-clause subsumption calls (NU) : 263078
% 2.85/3.08  # Rec. Clause-clause subsumption calls : 194778
% 2.85/3.08  # Non-unit clause-clause subsumptions  : 9962
% 2.85/3.08  # Unit Clause-clause subsumption calls : 3561
% 2.85/3.08  # Rewrite failures with RHS unbound    : 0
% 2.85/3.08  # BW rewrite match attempts            : 445
% 2.85/3.08  # BW rewrite match successes           : 65
% 2.85/3.08  # Condensation attempts                : 0
% 2.85/3.08  # Condensation successes               : 0
% 2.85/3.08  # Termbank termtop insertions          : 7426904
% 2.85/3.09  
% 2.85/3.09  # -------------------------------------------------
% 2.85/3.09  # User time                : 2.604 s
% 2.85/3.09  # System time              : 0.143 s
% 2.85/3.09  # Total time               : 2.747 s
% 2.85/3.09  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
