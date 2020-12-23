%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:27 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  101 (1534 expanded)
%              Number of clauses        :   56 ( 635 expanded)
%              Number of leaves         :   22 ( 449 expanded)
%              Depth                    :   15
%              Number of atoms          :  184 (2159 expanded)
%              Number of equality atoms :   85 (1084 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
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

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

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

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(t124_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(involutiveness_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k4_relat_1(k4_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(t140_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k8_relat_1(X1,X3),X2) = k8_relat_1(X1,k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(c_0_22,plain,(
    ! [X16,X17] : k1_setfam_1(k2_tarski(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_23,plain,(
    ! [X7,X8] : k1_enumset1(X7,X7,X8) = k2_tarski(X7,X8) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X46,X47] :
      ( ~ v1_relat_1(X47)
      | k1_relat_1(k7_relat_1(X47,X46)) = k3_xboole_0(k1_relat_1(X47),X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X9,X10,X11] : k2_enumset1(X9,X9,X10,X11) = k1_enumset1(X9,X10,X11) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X12,X13,X14,X15] : k3_enumset1(X12,X12,X13,X14,X15) = k2_enumset1(X12,X13,X14,X15) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X37)
      | ~ v1_relat_1(X38)
      | k4_relat_1(k5_relat_1(X37,X38)) = k5_relat_1(k4_relat_1(X38),k4_relat_1(X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_30,plain,(
    ! [X40] : k4_relat_1(k6_relat_1(X40)) = k6_relat_1(X40) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

fof(c_0_31,plain,(
    ! [X18] : v1_relat_1(k6_relat_1(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_32,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X44)
      | ~ r1_tarski(k1_relat_1(X44),X43)
      | k5_relat_1(k6_relat_1(X43),X44) = X44 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

fof(c_0_33,plain,(
    ! [X39] :
      ( k1_relat_1(k6_relat_1(X39)) = X39
      & k2_relat_1(k6_relat_1(X39)) = X39 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_34,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | v1_relat_1(k3_xboole_0(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

cnf(c_0_35,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_44,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | k8_relat_1(X28,X29) = k5_relat_1(X29,k6_relat_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_45,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X49)
      | k7_relat_1(X49,X48) = k5_relat_1(k6_relat_1(X48),X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_46,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | k8_relat_1(X30,X31) = k3_xboole_0(X31,k2_zfmisc_1(k1_relat_1(X31),X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).

cnf(c_0_47,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k3_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_49,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X1))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_50,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_41])])).

cnf(c_0_51,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( k8_relat_1(X2,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( v1_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_55,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_43]),c_0_41])])).

cnf(c_0_56,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_40]),c_0_40]),c_0_41])])).

cnf(c_0_57,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_41]),c_0_41])])).

cnf(c_0_58,plain,
    ( k8_relat_1(X2,X1) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_36]),c_0_37]),c_0_38])).

fof(c_0_59,plain,(
    ! [X35,X36] :
      ( ( r1_tarski(k1_relat_1(X35),k1_relat_1(X36))
        | ~ r1_tarski(X35,X36)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35) )
      & ( r1_tarski(k2_relat_1(X35),k2_relat_1(X36))
        | ~ r1_tarski(X35,X36)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_60,plain,
    ( v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_56]),c_0_57]),c_0_41])])).

fof(c_0_62,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | k4_relat_1(k4_relat_1(X21)) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

cnf(c_0_63,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_58])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,plain,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_43])).

cnf(c_0_66,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_67,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_51]),c_0_57]),c_0_40]),c_0_41]),c_0_41])])).

cnf(c_0_68,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_57]),c_0_41])])).

cnf(c_0_69,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X2) = X2
    | ~ r1_tarski(X2,X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_64]),c_0_65])).

fof(c_0_70,plain,(
    ! [X41,X42] :
      ( ( r1_tarski(k5_relat_1(X42,k6_relat_1(X41)),X42)
        | ~ v1_relat_1(X42) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X41),X42),X42)
        | ~ v1_relat_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

cnf(c_0_71,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])])).

fof(c_0_72,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

fof(c_0_73,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X24)
      | k7_relat_1(k7_relat_1(X24,X22),X23) = k7_relat_1(X24,k3_xboole_0(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

fof(c_0_74,plain,(
    ! [X25,X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ v1_relat_1(X27)
      | k7_relat_1(k5_relat_1(X26,X27),X25) = k5_relat_1(k7_relat_1(X26,X25),X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

cnf(c_0_75,plain,
    ( k5_relat_1(k6_relat_1(X1),X2) = X2
    | ~ r1_tarski(X2,k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_43]),c_0_41])])).

cnf(c_0_76,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_71]),c_0_40]),c_0_41])])).

fof(c_0_78,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_72])])])).

fof(c_0_79,plain,(
    ! [X45] :
      ( ~ v1_relat_1(X45)
      | k5_relat_1(X45,k6_relat_1(k2_relat_1(X45))) = X45 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_80,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_82,plain,
    ( k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_77]),c_0_41])])).

cnf(c_0_83,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_84,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_85,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_86,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_87,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_77]),c_0_41]),c_0_41])])).

cnf(c_0_88,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_82]),c_0_68])])).

fof(c_0_89,plain,(
    ! [X32,X33,X34] :
      ( ~ v1_relat_1(X34)
      | k7_relat_1(k8_relat_1(X32,X34),X33) = k8_relat_1(X32,k7_relat_1(X34,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).

cnf(c_0_90,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_91,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_52]),c_0_85]),c_0_41]),c_0_85]),c_0_41])])).

cnf(c_0_92,plain,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_86,c_0_55])).

cnf(c_0_93,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_82]),c_0_67]),c_0_77]),c_0_67]),c_0_77]),c_0_87]),c_0_68])]),c_0_88])).

cnf(c_0_94,plain,
    ( k7_relat_1(k8_relat_1(X2,X1),X3) = k8_relat_1(X2,k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),esk2_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_90,c_0_55])).

cnf(c_0_96,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X2) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_41])]),c_0_93])).

cnf(c_0_97,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X2) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_91]),c_0_41])]),c_0_57]),c_0_57])).

cnf(c_0_98,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),esk2_0))) != k7_relat_1(k6_relat_1(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_95,c_0_77])).

cnf(c_0_99,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_92]),c_0_91]),c_0_97]),c_0_41])])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_99])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___107_C12_02_nc_F1_PI_AE_Q4_CS_SP_PS_S06DN
% 0.13/0.40  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.027 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.40  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.13/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.40  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 0.13/0.40  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 0.13/0.40  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.40  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 0.13/0.40  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.13/0.40  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.13/0.40  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 0.13/0.40  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.13/0.40  fof(t124_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 0.13/0.40  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.13/0.40  fof(involutiveness_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k4_relat_1(k4_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 0.13/0.40  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 0.13/0.40  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 0.13/0.40  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 0.13/0.40  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 0.13/0.40  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 0.13/0.40  fof(t140_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k8_relat_1(X1,X3),X2)=k8_relat_1(X1,k7_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 0.13/0.40  fof(c_0_22, plain, ![X16, X17]:k1_setfam_1(k2_tarski(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.40  fof(c_0_23, plain, ![X7, X8]:k1_enumset1(X7,X7,X8)=k2_tarski(X7,X8), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.40  fof(c_0_24, plain, ![X46, X47]:(~v1_relat_1(X47)|k1_relat_1(k7_relat_1(X47,X46))=k3_xboole_0(k1_relat_1(X47),X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.13/0.40  cnf(c_0_25, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  fof(c_0_27, plain, ![X9, X10, X11]:k2_enumset1(X9,X9,X10,X11)=k1_enumset1(X9,X10,X11), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.40  fof(c_0_28, plain, ![X12, X13, X14, X15]:k3_enumset1(X12,X12,X13,X14,X15)=k2_enumset1(X12,X13,X14,X15), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.40  fof(c_0_29, plain, ![X37, X38]:(~v1_relat_1(X37)|(~v1_relat_1(X38)|k4_relat_1(k5_relat_1(X37,X38))=k5_relat_1(k4_relat_1(X38),k4_relat_1(X37)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.13/0.40  fof(c_0_30, plain, ![X40]:k4_relat_1(k6_relat_1(X40))=k6_relat_1(X40), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.13/0.40  fof(c_0_31, plain, ![X18]:v1_relat_1(k6_relat_1(X18)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.40  fof(c_0_32, plain, ![X43, X44]:(~v1_relat_1(X44)|(~r1_tarski(k1_relat_1(X44),X43)|k5_relat_1(k6_relat_1(X43),X44)=X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.13/0.40  fof(c_0_33, plain, ![X39]:(k1_relat_1(k6_relat_1(X39))=X39&k2_relat_1(k6_relat_1(X39))=X39), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.13/0.40  fof(c_0_34, plain, ![X19, X20]:(~v1_relat_1(X19)|v1_relat_1(k3_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.13/0.40  cnf(c_0_35, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_36, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.40  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.40  cnf(c_0_38, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.40  cnf(c_0_39, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.40  cnf(c_0_40, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.40  cnf(c_0_41, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.40  cnf(c_0_42, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.40  cnf(c_0_43, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.40  fof(c_0_44, plain, ![X28, X29]:(~v1_relat_1(X29)|k8_relat_1(X28,X29)=k5_relat_1(X29,k6_relat_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.13/0.40  fof(c_0_45, plain, ![X48, X49]:(~v1_relat_1(X49)|k7_relat_1(X49,X48)=k5_relat_1(k6_relat_1(X48),X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.13/0.40  fof(c_0_46, plain, ![X30, X31]:(~v1_relat_1(X31)|k8_relat_1(X30,X31)=k3_xboole_0(X31,k2_zfmisc_1(k1_relat_1(X31),X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).
% 0.13/0.40  cnf(c_0_47, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.40  cnf(c_0_48, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k3_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])).
% 0.13/0.40  cnf(c_0_49, plain, (k4_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k4_relat_1(X2),k6_relat_1(X1))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.13/0.40  cnf(c_0_50, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_41])])).
% 0.13/0.40  cnf(c_0_51, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.40  cnf(c_0_52, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.40  cnf(c_0_53, plain, (k8_relat_1(X2,X1)=k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.40  cnf(c_0_54, plain, (v1_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_36]), c_0_37]), c_0_38])).
% 0.13/0.40  cnf(c_0_55, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))=k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_43]), c_0_41])])).
% 0.13/0.40  cnf(c_0_56, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_40]), c_0_40]), c_0_41])])).
% 0.13/0.40  cnf(c_0_57, plain, (k8_relat_1(X1,k6_relat_1(X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_41]), c_0_41])])).
% 0.13/0.40  cnf(c_0_58, plain, (k8_relat_1(X2,X1)=k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_36]), c_0_37]), c_0_38])).
% 0.13/0.40  fof(c_0_59, plain, ![X35, X36]:((r1_tarski(k1_relat_1(X35),k1_relat_1(X36))|~r1_tarski(X35,X36)|~v1_relat_1(X36)|~v1_relat_1(X35))&(r1_tarski(k2_relat_1(X35),k2_relat_1(X36))|~r1_tarski(X35,X36)|~v1_relat_1(X36)|~v1_relat_1(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.13/0.40  cnf(c_0_60, plain, (v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.40  cnf(c_0_61, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_56]), c_0_57]), c_0_41])])).
% 0.13/0.40  fof(c_0_62, plain, ![X21]:(~v1_relat_1(X21)|k4_relat_1(k4_relat_1(X21))=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).
% 0.13/0.40  cnf(c_0_63, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_54, c_0_58])).
% 0.13/0.40  cnf(c_0_64, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.40  cnf(c_0_65, plain, (v1_relat_1(X1)|~r1_tarski(X1,X2)|~v1_relat_1(X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_43])).
% 0.13/0.40  cnf(c_0_66, plain, (k4_relat_1(k4_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.40  cnf(c_0_67, plain, (k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_51]), c_0_57]), c_0_40]), c_0_41]), c_0_41])])).
% 0.13/0.40  cnf(c_0_68, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_57]), c_0_41])])).
% 0.13/0.40  cnf(c_0_69, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X2)=X2|~r1_tarski(X2,X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_64]), c_0_65])).
% 0.13/0.40  fof(c_0_70, plain, ![X41, X42]:((r1_tarski(k5_relat_1(X42,k6_relat_1(X41)),X42)|~v1_relat_1(X42))&(r1_tarski(k5_relat_1(k6_relat_1(X41),X42),X42)|~v1_relat_1(X42))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.13/0.40  cnf(c_0_71, plain, (k4_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])])).
% 0.13/0.40  fof(c_0_72, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.13/0.40  fof(c_0_73, plain, ![X22, X23, X24]:(~v1_relat_1(X24)|k7_relat_1(k7_relat_1(X24,X22),X23)=k7_relat_1(X24,k3_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.13/0.40  fof(c_0_74, plain, ![X25, X26, X27]:(~v1_relat_1(X26)|(~v1_relat_1(X27)|k7_relat_1(k5_relat_1(X26,X27),X25)=k5_relat_1(k7_relat_1(X26,X25),X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 0.13/0.40  cnf(c_0_75, plain, (k5_relat_1(k6_relat_1(X1),X2)=X2|~r1_tarski(X2,k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_43]), c_0_41])])).
% 0.13/0.40  cnf(c_0_76, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.13/0.40  cnf(c_0_77, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_71]), c_0_40]), c_0_41])])).
% 0.13/0.40  fof(c_0_78, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_72])])])).
% 0.13/0.40  fof(c_0_79, plain, ![X45]:(~v1_relat_1(X45)|k5_relat_1(X45,k6_relat_1(k2_relat_1(X45)))=X45), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.13/0.40  cnf(c_0_80, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.13/0.40  cnf(c_0_81, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.13/0.40  cnf(c_0_82, plain, (k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_77]), c_0_41])])).
% 0.13/0.40  cnf(c_0_83, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.13/0.40  cnf(c_0_84, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.13/0.40  cnf(c_0_85, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.40  cnf(c_0_86, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_36]), c_0_37]), c_0_38])).
% 0.13/0.40  cnf(c_0_87, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3))=k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_77]), c_0_41]), c_0_41])])).
% 0.13/0.40  cnf(c_0_88, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_82]), c_0_68])])).
% 0.13/0.40  fof(c_0_89, plain, ![X32, X33, X34]:(~v1_relat_1(X34)|k7_relat_1(k8_relat_1(X32,X34),X33)=k8_relat_1(X32,k7_relat_1(X34,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).
% 0.13/0.40  cnf(c_0_90, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_36]), c_0_37]), c_0_38])).
% 0.13/0.40  cnf(c_0_91, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_52]), c_0_85]), c_0_41]), c_0_85]), c_0_41])])).
% 0.13/0.40  cnf(c_0_92, plain, (k7_relat_1(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))=k7_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_86, c_0_55])).
% 0.13/0.40  cnf(c_0_93, plain, (k7_relat_1(k6_relat_1(X1),X2)=k7_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_82]), c_0_67]), c_0_77]), c_0_67]), c_0_77]), c_0_87]), c_0_68])]), c_0_88])).
% 0.13/0.40  cnf(c_0_94, plain, (k7_relat_1(k8_relat_1(X2,X1),X3)=k8_relat_1(X2,k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.13/0.40  cnf(c_0_95, negated_conjecture, (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),esk2_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_90, c_0_55])).
% 0.13/0.40  cnf(c_0_96, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))),X2)=k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_41])]), c_0_93])).
% 0.13/0.40  cnf(c_0_97, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X2)=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_91]), c_0_41])]), c_0_57]), c_0_57])).
% 0.13/0.40  cnf(c_0_98, negated_conjecture, (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),esk2_0)))!=k7_relat_1(k6_relat_1(esk1_0),esk2_0)), inference(rw,[status(thm)],[c_0_95, c_0_77])).
% 0.13/0.40  cnf(c_0_99, plain, (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_92]), c_0_91]), c_0_97]), c_0_41])])).
% 0.13/0.40  cnf(c_0_100, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_99])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 101
% 0.13/0.40  # Proof object clause steps            : 56
% 0.13/0.40  # Proof object formula steps           : 45
% 0.13/0.40  # Proof object conjectures             : 8
% 0.13/0.40  # Proof object clause conjectures      : 5
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 23
% 0.13/0.40  # Proof object initial formulas used   : 22
% 0.13/0.40  # Proof object generating inferences   : 22
% 0.13/0.40  # Proof object simplifying inferences  : 87
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 23
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 26
% 0.13/0.40  # Removed in clause preprocessing      : 4
% 0.13/0.40  # Initial clauses in saturation        : 22
% 0.13/0.40  # Processed clauses                    : 291
% 0.13/0.40  # ...of these trivial                  : 15
% 0.13/0.40  # ...subsumed                          : 122
% 0.13/0.40  # ...remaining for further processing  : 154
% 0.13/0.40  # Other redundant clauses eliminated   : 0
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 1
% 0.13/0.40  # Backward-rewritten                   : 17
% 0.13/0.40  # Generated clauses                    : 1594
% 0.13/0.40  # ...of the previous two non-trivial   : 1028
% 0.13/0.40  # Contextual simplify-reflections      : 6
% 0.13/0.40  # Paramodulations                      : 1594
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 0
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 114
% 0.13/0.40  #    Positive orientable unit clauses  : 33
% 0.13/0.40  #    Positive unorientable unit clauses: 2
% 0.13/0.40  #    Negative unit clauses             : 2
% 0.13/0.40  #    Non-unit-clauses                  : 77
% 0.13/0.40  # Current number of unprocessed clauses: 747
% 0.13/0.40  # ...number of literals in the above   : 2040
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 44
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 661
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 586
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 118
% 0.13/0.40  # Unit Clause-clause subsumption calls : 25
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 78
% 0.13/0.40  # BW rewrite match successes           : 37
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 21451
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.048 s
% 0.13/0.40  # System time              : 0.007 s
% 0.13/0.40  # Total time               : 0.055 s
% 0.13/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
