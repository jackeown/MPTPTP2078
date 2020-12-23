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

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  110 (3141 expanded)
%              Number of clauses        :   67 (1322 expanded)
%              Number of leaves         :   21 ( 909 expanded)
%              Depth                    :   17
%              Number of atoms          :  204 (6201 expanded)
%              Number of equality atoms :   91 (1951 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc24_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v4_relat_1(k6_relat_1(X1),X1)
      & v5_relat_1(k6_relat_1(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(t72_relat_1,axiom,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(t140_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k8_relat_1(X1,X3),X2) = k8_relat_1(X1,k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(involutiveness_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k4_relat_1(k4_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t119_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k8_relat_1(X1,X2)) = k3_xboole_0(k2_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(c_0_21,plain,(
    ! [X20,X21] : k1_setfam_1(k2_tarski(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_22,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ v1_relat_1(X23)
      | v1_relat_1(k5_relat_1(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_24,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(X48)
      | k7_relat_1(X48,X47) = k5_relat_1(k6_relat_1(X47),X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_25,plain,(
    ! [X49] :
      ( v1_relat_1(k6_relat_1(X49))
      & v4_relat_1(k6_relat_1(X49),X49)
      & v5_relat_1(k6_relat_1(X49),X49) ) ),
    inference(variable_rename,[status(thm)],[fc24_relat_1])).

fof(c_0_26,plain,(
    ! [X25,X26,X27] :
      ( ~ v1_relat_1(X27)
      | k7_relat_1(k7_relat_1(X27,X25),X26) = k7_relat_1(X27,k3_xboole_0(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X8,X9,X10] : k2_enumset1(X8,X8,X9,X10) = k1_enumset1(X8,X9,X10) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X11,X12,X13,X14] : k3_enumset1(X11,X11,X12,X13,X14) = k2_enumset1(X11,X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_31,plain,(
    ! [X15,X16,X17,X18,X19] : k4_enumset1(X15,X15,X16,X17,X18,X19) = k3_enumset1(X15,X16,X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_32,plain,(
    ! [X41,X42] :
      ( ~ v1_relat_1(X41)
      | ~ v1_relat_1(X42)
      | k4_relat_1(k5_relat_1(X41,X42)) = k5_relat_1(k4_relat_1(X42),k4_relat_1(X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_33,plain,(
    ! [X44] : k4_relat_1(k6_relat_1(X44)) = k6_relat_1(X44) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

cnf(c_0_34,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_42,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | ~ v4_relat_1(X38,X37)
      | X38 = k7_relat_1(X38,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_43,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_46,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_47,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( v4_relat_1(k6_relat_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_49,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | k8_relat_1(X30,X31) = k5_relat_1(X31,k6_relat_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_50,plain,(
    ! [X34,X35,X36] :
      ( ~ v1_relat_1(X36)
      | k7_relat_1(k8_relat_1(X34,X36),X35) = k8_relat_1(X34,k7_relat_1(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).

fof(c_0_51,plain,(
    ! [X24] :
      ( ~ v1_relat_1(X24)
      | k4_relat_1(k4_relat_1(X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

cnf(c_0_52,plain,
    ( k4_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_36])])).

cnf(c_0_53,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_36])])).

cnf(c_0_55,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( k7_relat_1(k8_relat_1(X2,X1),X3) = k8_relat_1(X2,k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_35]),c_0_44]),c_0_36]),c_0_36])])).

cnf(c_0_59,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_36])])).

fof(c_0_60,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r1_tarski(k2_relat_1(X33),X32)
      | k8_relat_1(X32,X33) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

fof(c_0_61,plain,(
    ! [X43] :
      ( k1_relat_1(k6_relat_1(X43)) = X43
      & k2_relat_1(k6_relat_1(X43)) = X43 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_62,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | k2_relat_1(k8_relat_1(X28,X29)) = k3_xboole_0(k2_relat_1(X29),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).

cnf(c_0_63,plain,
    ( k7_relat_1(k8_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(X1))
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_45])).

cnf(c_0_64,plain,
    ( k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X2) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_54]),c_0_36])])).

cnf(c_0_65,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_66,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_68,plain,(
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

cnf(c_0_69,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k3_xboole_0(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_54]),c_0_36])])).

cnf(c_0_71,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_65]),c_0_44]),c_0_36])])).

cnf(c_0_72,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_36])])).

cnf(c_0_73,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_75,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X1))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_36])])).

cnf(c_0_77,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_72]),c_0_36])])).

cnf(c_0_78,plain,
    ( k8_relat_1(k2_relat_1(X1),X2) = X2
    | ~ r1_tarski(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_73])).

fof(c_0_79,plain,(
    ! [X45,X46] :
      ( ( r1_tarski(k5_relat_1(X46,k6_relat_1(X45)),X46)
        | ~ v1_relat_1(X46) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X45),X46),X46)
        | ~ v1_relat_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

fof(c_0_80,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

cnf(c_0_81,plain,
    ( k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)) = k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_67]),c_0_36])]),c_0_75])).

cnf(c_0_82,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_44]),c_0_44]),c_0_36])])).

cnf(c_0_83,plain,
    ( k8_relat_1(X1,X2) = X2
    | ~ r1_tarski(X2,k6_relat_1(X1))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_67]),c_0_36])])).

cnf(c_0_84,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_85,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_80])])])).

cnf(c_0_86,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X1),k2_relat_1(X2))) = k2_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[c_0_74,c_0_81])).

cnf(c_0_87,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_82]),c_0_36])])).

cnf(c_0_88,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_89,plain,
    ( k7_relat_1(k8_relat_1(X1,X2),X3) = k7_relat_1(X2,X3)
    | ~ r1_tarski(k7_relat_1(X2,X3),k6_relat_1(X1))
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_83]),c_0_45])).

cnf(c_0_90,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_35]),c_0_36]),c_0_36])])).

cnf(c_0_91,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_92,plain,
    ( k2_relat_1(k8_relat_1(X1,X2)) = X1
    | ~ r1_tarski(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_67])).

cnf(c_0_93,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_35])).

cnf(c_0_94,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_70]),c_0_71]),c_0_36])])).

cnf(c_0_95,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_96,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X1),X2) = k6_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_46]),c_0_36])])).

cnf(c_0_97,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_72]),c_0_67]),c_0_67]),c_0_36])])).

cnf(c_0_98,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_59])])).

cnf(c_0_99,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))) != k7_relat_1(k6_relat_1(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_95,c_0_71])).

cnf(c_0_100,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X2),X1) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_81]),c_0_81])).

cnf(c_0_101,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_98])])).

cnf(c_0_102,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_70]),c_0_70])).

cnf(c_0_103,negated_conjecture,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0))) != k7_relat_1(k6_relat_1(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_99,c_0_81])).

cnf(c_0_104,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))),X2) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ),
    inference(rw,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_105,plain,
    ( k7_relat_1(X1,k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_46,c_0_81])).

cnf(c_0_106,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X2) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_35]),c_0_36])])).

cnf(c_0_107,negated_conjecture,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0))) != k7_relat_1(k6_relat_1(esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_103,c_0_101])).

cnf(c_0_108,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_54]),c_0_106]),c_0_36])])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_108]),c_0_101])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:34:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.43  #
% 0.18/0.43  # Preprocessing time       : 0.028 s
% 0.18/0.43  # Presaturation interreduction done
% 0.18/0.43  
% 0.18/0.43  # Proof found!
% 0.18/0.43  # SZS status Theorem
% 0.18/0.43  # SZS output start CNFRefutation
% 0.18/0.43  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.18/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.43  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.18/0.43  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.18/0.43  fof(fc24_relat_1, axiom, ![X1]:((v1_relat_1(k6_relat_1(X1))&v4_relat_1(k6_relat_1(X1),X1))&v5_relat_1(k6_relat_1(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 0.18/0.43  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 0.18/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.43  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.43  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.18/0.43  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 0.18/0.43  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 0.18/0.43  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.18/0.43  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 0.18/0.43  fof(t140_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k8_relat_1(X1,X3),X2)=k8_relat_1(X1,k7_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 0.18/0.43  fof(involutiveness_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k4_relat_1(k4_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 0.18/0.43  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 0.18/0.43  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.18/0.43  fof(t119_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k8_relat_1(X1,X2))=k3_xboole_0(k2_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 0.18/0.43  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.18/0.43  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 0.18/0.43  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.18/0.43  fof(c_0_21, plain, ![X20, X21]:k1_setfam_1(k2_tarski(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.18/0.43  fof(c_0_22, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.43  fof(c_0_23, plain, ![X22, X23]:(~v1_relat_1(X22)|~v1_relat_1(X23)|v1_relat_1(k5_relat_1(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.18/0.43  fof(c_0_24, plain, ![X47, X48]:(~v1_relat_1(X48)|k7_relat_1(X48,X47)=k5_relat_1(k6_relat_1(X47),X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.18/0.43  fof(c_0_25, plain, ![X49]:((v1_relat_1(k6_relat_1(X49))&v4_relat_1(k6_relat_1(X49),X49))&v5_relat_1(k6_relat_1(X49),X49)), inference(variable_rename,[status(thm)],[fc24_relat_1])).
% 0.18/0.43  fof(c_0_26, plain, ![X25, X26, X27]:(~v1_relat_1(X27)|k7_relat_1(k7_relat_1(X27,X25),X26)=k7_relat_1(X27,k3_xboole_0(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.18/0.43  cnf(c_0_27, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.43  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.43  fof(c_0_29, plain, ![X8, X9, X10]:k2_enumset1(X8,X8,X9,X10)=k1_enumset1(X8,X9,X10), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.43  fof(c_0_30, plain, ![X11, X12, X13, X14]:k3_enumset1(X11,X11,X12,X13,X14)=k2_enumset1(X11,X12,X13,X14), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.43  fof(c_0_31, plain, ![X15, X16, X17, X18, X19]:k4_enumset1(X15,X15,X16,X17,X18,X19)=k3_enumset1(X15,X16,X17,X18,X19), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.18/0.43  fof(c_0_32, plain, ![X41, X42]:(~v1_relat_1(X41)|(~v1_relat_1(X42)|k4_relat_1(k5_relat_1(X41,X42))=k5_relat_1(k4_relat_1(X42),k4_relat_1(X41)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.18/0.43  fof(c_0_33, plain, ![X44]:k4_relat_1(k6_relat_1(X44))=k6_relat_1(X44), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.18/0.43  cnf(c_0_34, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.43  cnf(c_0_35, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.43  cnf(c_0_36, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.43  cnf(c_0_37, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.43  cnf(c_0_38, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.43  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.43  cnf(c_0_40, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.43  cnf(c_0_41, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.43  fof(c_0_42, plain, ![X37, X38]:(~v1_relat_1(X38)|~v4_relat_1(X38,X37)|X38=k7_relat_1(X38,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.18/0.43  cnf(c_0_43, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.43  cnf(c_0_44, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.43  cnf(c_0_45, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.18/0.43  cnf(c_0_46, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.18/0.43  cnf(c_0_47, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.43  cnf(c_0_48, plain, (v4_relat_1(k6_relat_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.43  fof(c_0_49, plain, ![X30, X31]:(~v1_relat_1(X31)|k8_relat_1(X30,X31)=k5_relat_1(X31,k6_relat_1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.18/0.43  fof(c_0_50, plain, ![X34, X35, X36]:(~v1_relat_1(X36)|k7_relat_1(k8_relat_1(X34,X36),X35)=k8_relat_1(X34,k7_relat_1(X36,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).
% 0.18/0.43  fof(c_0_51, plain, ![X24]:(~v1_relat_1(X24)|k4_relat_1(k4_relat_1(X24))=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).
% 0.18/0.43  cnf(c_0_52, plain, (k4_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k5_relat_1(k6_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_36])])).
% 0.18/0.43  cnf(c_0_53, plain, (v1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.18/0.43  cnf(c_0_54, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_36])])).
% 0.18/0.43  cnf(c_0_55, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.18/0.43  cnf(c_0_56, plain, (k7_relat_1(k8_relat_1(X2,X1),X3)=k8_relat_1(X2,k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.18/0.43  cnf(c_0_57, plain, (k4_relat_1(k4_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.18/0.43  cnf(c_0_58, plain, (k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_35]), c_0_44]), c_0_36]), c_0_36])])).
% 0.18/0.43  cnf(c_0_59, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_36])])).
% 0.18/0.43  fof(c_0_60, plain, ![X32, X33]:(~v1_relat_1(X33)|(~r1_tarski(k2_relat_1(X33),X32)|k8_relat_1(X32,X33)=X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.18/0.43  fof(c_0_61, plain, ![X43]:(k1_relat_1(k6_relat_1(X43))=X43&k2_relat_1(k6_relat_1(X43))=X43), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.18/0.43  fof(c_0_62, plain, ![X28, X29]:(~v1_relat_1(X29)|k2_relat_1(k8_relat_1(X28,X29))=k3_xboole_0(k2_relat_1(X29),X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).
% 0.18/0.43  cnf(c_0_63, plain, (k7_relat_1(k8_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X2,X3),k6_relat_1(X1))|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_45])).
% 0.18/0.43  cnf(c_0_64, plain, (k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X2)=k8_relat_1(X1,k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_54]), c_0_36])])).
% 0.18/0.43  cnf(c_0_65, plain, (k4_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.18/0.43  cnf(c_0_66, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.18/0.43  cnf(c_0_67, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.18/0.43  fof(c_0_68, plain, ![X39, X40]:((r1_tarski(k1_relat_1(X39),k1_relat_1(X40))|~r1_tarski(X39,X40)|~v1_relat_1(X40)|~v1_relat_1(X39))&(r1_tarski(k2_relat_1(X39),k2_relat_1(X40))|~r1_tarski(X39,X40)|~v1_relat_1(X40)|~v1_relat_1(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.18/0.43  cnf(c_0_69, plain, (k2_relat_1(k8_relat_1(X2,X1))=k3_xboole_0(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.18/0.43  cnf(c_0_70, plain, (k8_relat_1(X1,k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_54]), c_0_36])])).
% 0.18/0.43  cnf(c_0_71, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_65]), c_0_44]), c_0_36])])).
% 0.18/0.43  cnf(c_0_72, plain, (k8_relat_1(X1,k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_36])])).
% 0.18/0.43  cnf(c_0_73, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.18/0.43  cnf(c_0_74, plain, (k2_relat_1(k8_relat_1(X2,X1))=k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.18/0.43  cnf(c_0_75, plain, (k8_relat_1(X1,k6_relat_1(X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.18/0.43  cnf(c_0_76, plain, (k4_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k4_relat_1(X2),k6_relat_1(X1))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_36])])).
% 0.18/0.43  cnf(c_0_77, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_72]), c_0_36])])).
% 0.18/0.43  cnf(c_0_78, plain, (k8_relat_1(k2_relat_1(X1),X2)=X2|~r1_tarski(X2,X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_73])).
% 0.18/0.43  fof(c_0_79, plain, ![X45, X46]:((r1_tarski(k5_relat_1(X46,k6_relat_1(X45)),X46)|~v1_relat_1(X46))&(r1_tarski(k5_relat_1(k6_relat_1(X45),X46),X46)|~v1_relat_1(X46))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.18/0.43  fof(c_0_80, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.18/0.43  cnf(c_0_81, plain, (k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))=k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_67]), c_0_36])]), c_0_75])).
% 0.18/0.43  cnf(c_0_82, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_44]), c_0_44]), c_0_36])])).
% 0.18/0.43  cnf(c_0_83, plain, (k8_relat_1(X1,X2)=X2|~r1_tarski(X2,k6_relat_1(X1))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_67]), c_0_36])])).
% 0.18/0.43  cnf(c_0_84, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.18/0.43  fof(c_0_85, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_80])])])).
% 0.18/0.43  cnf(c_0_86, plain, (k2_relat_1(k7_relat_1(k6_relat_1(X1),k2_relat_1(X2)))=k2_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(rw,[status(thm)],[c_0_74, c_0_81])).
% 0.18/0.43  cnf(c_0_87, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_82]), c_0_36])])).
% 0.18/0.43  cnf(c_0_88, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.18/0.43  cnf(c_0_89, plain, (k7_relat_1(k8_relat_1(X1,X2),X3)=k7_relat_1(X2,X3)|~r1_tarski(k7_relat_1(X2,X3),k6_relat_1(X1))|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_83]), c_0_45])).
% 0.18/0.43  cnf(c_0_90, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_35]), c_0_36]), c_0_36])])).
% 0.18/0.43  cnf(c_0_91, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.18/0.43  cnf(c_0_92, plain, (k2_relat_1(k8_relat_1(X1,X2))=X1|~r1_tarski(X1,k2_relat_1(X2))|~v1_relat_1(X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_67])).
% 0.18/0.43  cnf(c_0_93, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_88, c_0_35])).
% 0.18/0.43  cnf(c_0_94, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_70]), c_0_71]), c_0_36])])).
% 0.18/0.43  cnf(c_0_95, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.18/0.43  cnf(c_0_96, plain, (k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))),X1),X2)=k6_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_46]), c_0_36])])).
% 0.18/0.43  cnf(c_0_97, plain, (X1=X2|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_72]), c_0_67]), c_0_67]), c_0_36])])).
% 0.18/0.43  cnf(c_0_98, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k7_relat_1(k6_relat_1(X2),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_59])])).
% 0.18/0.43  cnf(c_0_99, negated_conjecture, (k6_relat_1(k1_setfam_1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))!=k7_relat_1(k6_relat_1(esk1_0),esk2_0)), inference(rw,[status(thm)],[c_0_95, c_0_71])).
% 0.18/0.43  cnf(c_0_100, plain, (k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X2),X1)=k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_81]), c_0_81])).
% 0.18/0.43  cnf(c_0_101, plain, (k7_relat_1(k6_relat_1(X1),X2)=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_98])])).
% 0.18/0.43  cnf(c_0_102, plain, (k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X1)=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_70]), c_0_70])).
% 0.18/0.43  cnf(c_0_103, negated_conjecture, (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0)))!=k7_relat_1(k6_relat_1(esk1_0),esk2_0)), inference(rw,[status(thm)],[c_0_99, c_0_81])).
% 0.18/0.43  cnf(c_0_104, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))),X2)=k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)))), inference(rw,[status(thm)],[c_0_100, c_0_101])).
% 0.18/0.43  cnf(c_0_105, plain, (k7_relat_1(X1,k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)))=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_46, c_0_81])).
% 0.18/0.43  cnf(c_0_106, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X2)=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_35]), c_0_36])])).
% 0.18/0.43  cnf(c_0_107, negated_conjecture, (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0)))!=k7_relat_1(k6_relat_1(esk2_0),esk1_0)), inference(rw,[status(thm)],[c_0_103, c_0_101])).
% 0.18/0.43  cnf(c_0_108, plain, (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)))=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_54]), c_0_106]), c_0_36])])).
% 0.18/0.43  cnf(c_0_109, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_108]), c_0_101])]), ['proof']).
% 0.18/0.43  # SZS output end CNFRefutation
% 0.18/0.43  # Proof object total steps             : 110
% 0.18/0.43  # Proof object clause steps            : 67
% 0.18/0.43  # Proof object formula steps           : 43
% 0.18/0.43  # Proof object conjectures             : 9
% 0.18/0.43  # Proof object clause conjectures      : 6
% 0.18/0.43  # Proof object formula conjectures     : 3
% 0.18/0.43  # Proof object initial clauses used    : 23
% 0.18/0.43  # Proof object initial formulas used   : 21
% 0.18/0.43  # Proof object generating inferences   : 30
% 0.18/0.43  # Proof object simplifying inferences  : 92
% 0.18/0.43  # Training examples: 0 positive, 0 negative
% 0.18/0.43  # Parsed axioms                        : 21
% 0.18/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.43  # Initial clauses                      : 26
% 0.18/0.43  # Removed in clause preprocessing      : 5
% 0.18/0.43  # Initial clauses in saturation        : 21
% 0.18/0.43  # Processed clauses                    : 529
% 0.18/0.43  # ...of these trivial                  : 8
% 0.18/0.43  # ...subsumed                          : 274
% 0.18/0.43  # ...remaining for further processing  : 247
% 0.18/0.43  # Other redundant clauses eliminated   : 0
% 0.18/0.43  # Clauses deleted for lack of memory   : 0
% 0.18/0.43  # Backward-subsumed                    : 9
% 0.18/0.43  # Backward-rewritten                   : 33
% 0.18/0.43  # Generated clauses                    : 3713
% 0.18/0.43  # ...of the previous two non-trivial   : 3026
% 0.18/0.43  # Contextual simplify-reflections      : 6
% 0.18/0.43  # Paramodulations                      : 3713
% 0.18/0.43  # Factorizations                       : 0
% 0.18/0.43  # Equation resolutions                 : 0
% 0.18/0.43  # Propositional unsat checks           : 0
% 0.18/0.43  #    Propositional check models        : 0
% 0.18/0.43  #    Propositional check unsatisfiable : 0
% 0.18/0.43  #    Propositional clauses             : 0
% 0.18/0.43  #    Propositional clauses after purity: 0
% 0.18/0.43  #    Propositional unsat core size     : 0
% 0.18/0.43  #    Propositional preprocessing time  : 0.000
% 0.18/0.43  #    Propositional encoding time       : 0.000
% 0.18/0.43  #    Propositional solver time         : 0.000
% 0.18/0.43  #    Success case prop preproc time    : 0.000
% 0.18/0.43  #    Success case prop encoding time   : 0.000
% 0.18/0.43  #    Success case prop solver time     : 0.000
% 0.18/0.43  # Current number of processed clauses  : 184
% 0.18/0.43  #    Positive orientable unit clauses  : 27
% 0.18/0.43  #    Positive unorientable unit clauses: 1
% 0.18/0.43  #    Negative unit clauses             : 2
% 0.18/0.43  #    Non-unit-clauses                  : 154
% 0.18/0.43  # Current number of unprocessed clauses: 2496
% 0.18/0.43  # ...number of literals in the above   : 7904
% 0.18/0.43  # Current number of archived formulas  : 0
% 0.18/0.43  # Current number of archived clauses   : 68
% 0.18/0.43  # Clause-clause subsumption calls (NU) : 2065
% 0.18/0.43  # Rec. Clause-clause subsumption calls : 1830
% 0.18/0.43  # Non-unit clause-clause subsumptions  : 277
% 0.18/0.43  # Unit Clause-clause subsumption calls : 30
% 0.18/0.43  # Rewrite failures with RHS unbound    : 0
% 0.18/0.43  # BW rewrite match attempts            : 87
% 0.18/0.43  # BW rewrite match successes           : 54
% 0.18/0.43  # Condensation attempts                : 0
% 0.18/0.43  # Condensation successes               : 0
% 0.18/0.43  # Termbank termtop insertions          : 55795
% 0.18/0.43  
% 0.18/0.43  # -------------------------------------------------
% 0.18/0.43  # User time                : 0.087 s
% 0.18/0.43  # System time              : 0.008 s
% 0.18/0.43  # Total time               : 0.094 s
% 0.18/0.43  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
