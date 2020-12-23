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
% DateTime   : Thu Dec  3 10:53:34 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 (14228 expanded)
%              Number of clauses        :   62 (6261 expanded)
%              Number of leaves         :   20 (3983 expanded)
%              Depth                    :   20
%              Number of atoms          :  176 (21399 expanded)
%              Number of equality atoms :   85 (11293 expanded)
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

fof(t119_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k8_relat_1(X1,X2)) = k3_xboole_0(k2_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t124_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t140_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k8_relat_1(X1,X3),X2) = k8_relat_1(X1,k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

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

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(c_0_20,plain,(
    ! [X11,X12] : k1_setfam_1(k2_tarski(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_21,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | k2_relat_1(k8_relat_1(X20,X21)) = k3_xboole_0(k2_relat_1(X21),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X8,X9,X10] : k2_enumset1(X8,X8,X9,X10) = k1_enumset1(X8,X9,X10) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X4,X5] : r1_tarski(k3_xboole_0(X4,X5),X4) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_27,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k3_xboole_0(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X36] :
      ( k1_relat_1(k6_relat_1(X36)) = X36
      & k2_relat_1(k6_relat_1(X36)) = X36 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_31,plain,(
    ! [X41] :
      ( v1_relat_1(k6_relat_1(X41))
      & v1_funct_1(k6_relat_1(X41)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_34,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_28]),c_0_29])).

cnf(c_0_37,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

fof(c_0_38,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | k8_relat_1(X22,X23) = k5_relat_1(X23,k6_relat_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_39,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | v1_relat_1(k3_xboole_0(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_40,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k8_relat_1(X24,X25) = k3_xboole_0(X25,k2_zfmisc_1(k1_relat_1(X25),X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).

fof(c_0_41,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ r1_tarski(k2_relat_1(X27),X26)
      | k8_relat_1(X26,X27) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X38] :
      ( ~ v1_relat_1(X38)
      | k5_relat_1(X38,k6_relat_1(k2_relat_1(X38))) = X38 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_45,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X19)
      | k7_relat_1(k7_relat_1(X19,X17),X18) = k7_relat_1(X19,k3_xboole_0(X17,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_46,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( k8_relat_1(X2,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35])])).

cnf(c_0_50,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_52,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X40)
      | k7_relat_1(X40,X39) = k5_relat_1(k6_relat_1(X39),X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_53,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_relat_1(X30)
      | k7_relat_1(k8_relat_1(X28,X30),X29) = k8_relat_1(X28,k7_relat_1(X30,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).

cnf(c_0_54,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_28]),c_0_29])).

cnf(c_0_55,plain,
    ( k8_relat_1(X2,X1) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_28]),c_0_29])).

cnf(c_0_56,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_34]),c_0_35])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_34]),c_0_35])])).

cnf(c_0_58,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_28]),c_0_29])).

cnf(c_0_59,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( k7_relat_1(k8_relat_1(X2,X1),X3) = k8_relat_1(X2,k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,plain,
    ( k8_relat_1(X1,k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( k7_relat_1(X1,k2_relat_1(k8_relat_1(X2,k6_relat_1(X3)))) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_58,c_0_37])).

cnf(c_0_64,plain,
    ( k8_relat_1(X1,k7_relat_1(X2,X3)) = k5_relat_1(k6_relat_1(X3),k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_65,plain,
    ( k8_relat_1(X1,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_62]),c_0_35])])).

cnf(c_0_66,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_62]),c_0_34])).

cnf(c_0_67,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_62]),c_0_35])])).

fof(c_0_68,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ v1_relat_1(X32)
      | k4_relat_1(k5_relat_1(X31,X32)) = k5_relat_1(k4_relat_1(X32),k4_relat_1(X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_69,plain,(
    ! [X37] : k4_relat_1(k6_relat_1(X37)) = k6_relat_1(X37) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

cnf(c_0_70,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_35])])).

cnf(c_0_71,plain,
    ( k7_relat_1(k5_relat_1(X1,k6_relat_1(X2)),X3) = k8_relat_1(X2,k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_43])).

cnf(c_0_72,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_34]),c_0_35])])).

cnf(c_0_73,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_75,plain,(
    ! [X33,X34,X35] :
      ( ~ v1_relat_1(X33)
      | ~ v1_relat_1(X34)
      | ~ v1_relat_1(X35)
      | k5_relat_1(k5_relat_1(X33,X34),X35) = k5_relat_1(X33,k5_relat_1(X34,X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

fof(c_0_76,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | v1_relat_1(k5_relat_1(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_77,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

cnf(c_0_78,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_67]),c_0_72]),c_0_35])])).

cnf(c_0_79,plain,
    ( k4_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_35])])).

cnf(c_0_80,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_81,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

fof(c_0_82,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_77])])])).

cnf(c_0_83,plain,
    ( k8_relat_1(X1,k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) = k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X3),k6_relat_1(X1))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_67]),c_0_35])]),c_0_78])).

cnf(c_0_84,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_78]),c_0_35])])).

cnf(c_0_85,plain,
    ( k4_relat_1(k5_relat_1(X1,k5_relat_1(X2,k6_relat_1(X3)))) = k5_relat_1(k6_relat_1(X3),k4_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_35])]),c_0_81])).

cnf(c_0_86,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_72]),c_0_35])])).

cnf(c_0_87,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_88,plain,
    ( k8_relat_1(k2_relat_1(X1),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_57])).

cnf(c_0_89,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_83]),c_0_84])])).

cnf(c_0_90,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_72]),c_0_74]),c_0_35]),c_0_35])])).

cnf(c_0_91,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_28]),c_0_29])).

cnf(c_0_92,plain,
    ( k8_relat_1(k2_relat_1(X1),k7_relat_1(X1,X2)) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_88])).

cnf(c_0_93,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_56,c_0_78])).

cnf(c_0_94,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_89]),c_0_90]),c_0_90]),c_0_89]),c_0_35]),c_0_35])])).

cnf(c_0_95,negated_conjecture,
    ( k6_relat_1(k2_relat_1(k8_relat_1(esk2_0,k6_relat_1(esk1_0)))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_91,c_0_37])).

cnf(c_0_96,plain,
    ( k8_relat_1(k2_relat_1(X1),k5_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_59])).

cnf(c_0_97,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))) = k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_49]),c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0)))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_43]),c_0_35])])).

cnf(c_0_99,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_89]),c_0_83]),c_0_97]),c_0_84])])).

cnf(c_0_100,negated_conjecture,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_98,c_0_94])).

cnf(c_0_101,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_94]),c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:23:27 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.54  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.54  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.54  #
% 0.21/0.54  # Preprocessing time       : 0.035 s
% 0.21/0.54  # Presaturation interreduction done
% 0.21/0.54  
% 0.21/0.54  # Proof found!
% 0.21/0.54  # SZS status Theorem
% 0.21/0.54  # SZS output start CNFRefutation
% 0.21/0.54  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.21/0.54  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.54  fof(t119_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k8_relat_1(X1,X2))=k3_xboole_0(k2_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 0.21/0.54  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.54  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.21/0.54  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.21/0.54  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.21/0.54  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 0.21/0.54  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.21/0.54  fof(t124_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_relat_1)).
% 0.21/0.54  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 0.21/0.54  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 0.21/0.54  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 0.21/0.54  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.21/0.54  fof(t140_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k8_relat_1(X1,X3),X2)=k8_relat_1(X1,k7_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 0.21/0.54  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 0.21/0.54  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 0.21/0.54  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 0.21/0.54  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.21/0.54  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.21/0.54  fof(c_0_20, plain, ![X11, X12]:k1_setfam_1(k2_tarski(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.21/0.54  fof(c_0_21, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.54  fof(c_0_22, plain, ![X20, X21]:(~v1_relat_1(X21)|k2_relat_1(k8_relat_1(X20,X21))=k3_xboole_0(k2_relat_1(X21),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).
% 0.21/0.54  cnf(c_0_23, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.54  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.54  fof(c_0_25, plain, ![X8, X9, X10]:k2_enumset1(X8,X8,X9,X10)=k1_enumset1(X8,X9,X10), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.54  fof(c_0_26, plain, ![X4, X5]:r1_tarski(k3_xboole_0(X4,X5),X4), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.21/0.54  cnf(c_0_27, plain, (k2_relat_1(k8_relat_1(X2,X1))=k3_xboole_0(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.54  cnf(c_0_28, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.54  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.54  fof(c_0_30, plain, ![X36]:(k1_relat_1(k6_relat_1(X36))=X36&k2_relat_1(k6_relat_1(X36))=X36), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.21/0.54  fof(c_0_31, plain, ![X41]:(v1_relat_1(k6_relat_1(X41))&v1_funct_1(k6_relat_1(X41))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.21/0.54  cnf(c_0_32, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.54  cnf(c_0_33, plain, (k2_relat_1(k8_relat_1(X2,X1))=k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.21/0.54  cnf(c_0_34, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.54  cnf(c_0_35, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.54  cnf(c_0_36, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_28]), c_0_29])).
% 0.21/0.54  cnf(c_0_37, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k2_relat_1(k8_relat_1(X2,k6_relat_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.21/0.54  fof(c_0_38, plain, ![X22, X23]:(~v1_relat_1(X23)|k8_relat_1(X22,X23)=k5_relat_1(X23,k6_relat_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.21/0.54  fof(c_0_39, plain, ![X15, X16]:(~v1_relat_1(X15)|v1_relat_1(k3_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.21/0.54  fof(c_0_40, plain, ![X24, X25]:(~v1_relat_1(X25)|k8_relat_1(X24,X25)=k3_xboole_0(X25,k2_zfmisc_1(k1_relat_1(X25),X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).
% 0.21/0.54  fof(c_0_41, plain, ![X26, X27]:(~v1_relat_1(X27)|(~r1_tarski(k2_relat_1(X27),X26)|k8_relat_1(X26,X27)=X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.21/0.54  cnf(c_0_42, plain, (r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X2)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.54  cnf(c_0_43, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.54  fof(c_0_44, plain, ![X38]:(~v1_relat_1(X38)|k5_relat_1(X38,k6_relat_1(k2_relat_1(X38)))=X38), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.21/0.54  fof(c_0_45, plain, ![X17, X18, X19]:(~v1_relat_1(X19)|k7_relat_1(k7_relat_1(X19,X17),X18)=k7_relat_1(X19,k3_xboole_0(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.21/0.54  cnf(c_0_46, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.54  cnf(c_0_47, plain, (k8_relat_1(X2,X1)=k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.54  cnf(c_0_48, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.54  cnf(c_0_49, plain, (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_35])])).
% 0.21/0.54  cnf(c_0_50, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.54  cnf(c_0_51, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.54  fof(c_0_52, plain, ![X39, X40]:(~v1_relat_1(X40)|k7_relat_1(X40,X39)=k5_relat_1(k6_relat_1(X39),X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.21/0.54  fof(c_0_53, plain, ![X28, X29, X30]:(~v1_relat_1(X30)|k7_relat_1(k8_relat_1(X28,X30),X29)=k8_relat_1(X28,k7_relat_1(X30,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).
% 0.21/0.54  cnf(c_0_54, plain, (v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_28]), c_0_29])).
% 0.21/0.54  cnf(c_0_55, plain, (k8_relat_1(X2,X1)=k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_28]), c_0_29])).
% 0.21/0.54  cnf(c_0_56, plain, (k8_relat_1(X1,k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_34]), c_0_35])])).
% 0.21/0.54  cnf(c_0_57, plain, (r1_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_34]), c_0_35])])).
% 0.21/0.54  cnf(c_0_58, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_28]), c_0_29])).
% 0.21/0.54  cnf(c_0_59, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.54  cnf(c_0_60, plain, (k7_relat_1(k8_relat_1(X2,X1),X3)=k8_relat_1(X2,k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.54  cnf(c_0_61, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.54  cnf(c_0_62, plain, (k8_relat_1(X1,k6_relat_1(X1))=k6_relat_1(X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.54  cnf(c_0_63, plain, (k7_relat_1(X1,k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))))=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_58, c_0_37])).
% 0.21/0.54  cnf(c_0_64, plain, (k8_relat_1(X1,k7_relat_1(X2,X3))=k5_relat_1(k6_relat_1(X3),k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.21/0.54  cnf(c_0_65, plain, (k8_relat_1(X1,k7_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_62]), c_0_35])])).
% 0.21/0.54  cnf(c_0_66, plain, (k7_relat_1(k7_relat_1(X1,X2),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_62]), c_0_34])).
% 0.21/0.54  cnf(c_0_67, plain, (k7_relat_1(k6_relat_1(X1),X2)=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_62]), c_0_35])])).
% 0.21/0.54  fof(c_0_68, plain, ![X31, X32]:(~v1_relat_1(X31)|(~v1_relat_1(X32)|k4_relat_1(k5_relat_1(X31,X32))=k5_relat_1(k4_relat_1(X32),k4_relat_1(X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.21/0.54  fof(c_0_69, plain, ![X37]:k4_relat_1(k6_relat_1(X37))=k6_relat_1(X37), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.21/0.54  cnf(c_0_70, plain, (k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X1)=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_35])])).
% 0.21/0.54  cnf(c_0_71, plain, (k7_relat_1(k5_relat_1(X1,k6_relat_1(X2)),X3)=k8_relat_1(X2,k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_60, c_0_43])).
% 0.21/0.54  cnf(c_0_72, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_34]), c_0_35])])).
% 0.21/0.54  cnf(c_0_73, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.21/0.54  cnf(c_0_74, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.21/0.54  fof(c_0_75, plain, ![X33, X34, X35]:(~v1_relat_1(X33)|(~v1_relat_1(X34)|(~v1_relat_1(X35)|k5_relat_1(k5_relat_1(X33,X34),X35)=k5_relat_1(X33,k5_relat_1(X34,X35))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.21/0.54  fof(c_0_76, plain, ![X13, X14]:(~v1_relat_1(X13)|~v1_relat_1(X14)|v1_relat_1(k5_relat_1(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.21/0.54  fof(c_0_77, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.21/0.54  cnf(c_0_78, plain, (k8_relat_1(X1,k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_67]), c_0_72]), c_0_35])])).
% 0.21/0.54  cnf(c_0_79, plain, (k4_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k5_relat_1(k6_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_35])])).
% 0.21/0.54  cnf(c_0_80, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.21/0.54  cnf(c_0_81, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.21/0.54  fof(c_0_82, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_77])])])).
% 0.21/0.54  cnf(c_0_83, plain, (k8_relat_1(X1,k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))=k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X3),k6_relat_1(X1)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_67]), c_0_35])]), c_0_78])).
% 0.21/0.54  cnf(c_0_84, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_78]), c_0_35])])).
% 0.21/0.54  cnf(c_0_85, plain, (k4_relat_1(k5_relat_1(X1,k5_relat_1(X2,k6_relat_1(X3))))=k5_relat_1(k6_relat_1(X3),k4_relat_1(k5_relat_1(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_35])]), c_0_81])).
% 0.21/0.54  cnf(c_0_86, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k6_relat_1(X1),X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_72]), c_0_35])])).
% 0.21/0.54  cnf(c_0_87, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.21/0.54  cnf(c_0_88, plain, (k8_relat_1(k2_relat_1(X1),X1)=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_57])).
% 0.21/0.54  cnf(c_0_89, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_83]), c_0_84])])).
% 0.21/0.54  cnf(c_0_90, plain, (k4_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_72]), c_0_74]), c_0_35]), c_0_35])])).
% 0.21/0.54  cnf(c_0_91, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_28]), c_0_29])).
% 0.21/0.54  cnf(c_0_92, plain, (k8_relat_1(k2_relat_1(X1),k7_relat_1(X1,X2))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_60, c_0_88])).
% 0.21/0.54  cnf(c_0_93, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_56, c_0_78])).
% 0.21/0.54  cnf(c_0_94, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_89]), c_0_90]), c_0_90]), c_0_89]), c_0_35]), c_0_35])])).
% 0.21/0.54  cnf(c_0_95, negated_conjecture, (k6_relat_1(k2_relat_1(k8_relat_1(esk2_0,k6_relat_1(esk1_0))))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_91, c_0_37])).
% 0.21/0.54  cnf(c_0_96, plain, (k8_relat_1(k2_relat_1(X1),k5_relat_1(k6_relat_1(X2),X1))=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_92, c_0_59])).
% 0.21/0.54  cnf(c_0_97, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))))=k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_49]), c_0_94])).
% 0.21/0.54  cnf(c_0_98, negated_conjecture, (k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(esk1_0),k6_relat_1(esk2_0))))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_43]), c_0_35])])).
% 0.21/0.54  cnf(c_0_99, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_89]), c_0_83]), c_0_97]), c_0_84])])).
% 0.21/0.54  cnf(c_0_100, negated_conjecture, (k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_98, c_0_94])).
% 0.21/0.54  cnf(c_0_101, plain, (k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_94]), c_0_97])).
% 0.21/0.54  cnf(c_0_102, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_101])]), ['proof']).
% 0.21/0.54  # SZS output end CNFRefutation
% 0.21/0.54  # Proof object total steps             : 103
% 0.21/0.54  # Proof object clause steps            : 62
% 0.21/0.54  # Proof object formula steps           : 41
% 0.21/0.54  # Proof object conjectures             : 9
% 0.21/0.54  # Proof object clause conjectures      : 6
% 0.21/0.54  # Proof object formula conjectures     : 3
% 0.21/0.54  # Proof object initial clauses used    : 20
% 0.21/0.54  # Proof object initial formulas used   : 20
% 0.21/0.54  # Proof object generating inferences   : 29
% 0.21/0.54  # Proof object simplifying inferences  : 78
% 0.21/0.54  # Training examples: 0 positive, 0 negative
% 0.21/0.54  # Parsed axioms                        : 20
% 0.21/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.54  # Initial clauses                      : 22
% 0.21/0.54  # Removed in clause preprocessing      : 3
% 0.21/0.54  # Initial clauses in saturation        : 19
% 0.21/0.54  # Processed clauses                    : 964
% 0.21/0.54  # ...of these trivial                  : 195
% 0.21/0.54  # ...subsumed                          : 456
% 0.21/0.54  # ...remaining for further processing  : 313
% 0.21/0.54  # Other redundant clauses eliminated   : 0
% 0.21/0.54  # Clauses deleted for lack of memory   : 0
% 0.21/0.54  # Backward-subsumed                    : 10
% 0.21/0.54  # Backward-rewritten                   : 42
% 0.21/0.54  # Generated clauses                    : 8881
% 0.21/0.54  # ...of the previous two non-trivial   : 5461
% 0.21/0.54  # Contextual simplify-reflections      : 62
% 0.21/0.54  # Paramodulations                      : 8881
% 0.21/0.54  # Factorizations                       : 0
% 0.21/0.54  # Equation resolutions                 : 0
% 0.21/0.54  # Propositional unsat checks           : 0
% 0.21/0.54  #    Propositional check models        : 0
% 0.21/0.54  #    Propositional check unsatisfiable : 0
% 0.21/0.54  #    Propositional clauses             : 0
% 0.21/0.54  #    Propositional clauses after purity: 0
% 0.21/0.54  #    Propositional unsat core size     : 0
% 0.21/0.54  #    Propositional preprocessing time  : 0.000
% 0.21/0.54  #    Propositional encoding time       : 0.000
% 0.21/0.54  #    Propositional solver time         : 0.000
% 0.21/0.54  #    Success case prop preproc time    : 0.000
% 0.21/0.54  #    Success case prop encoding time   : 0.000
% 0.21/0.54  #    Success case prop solver time     : 0.000
% 0.21/0.54  # Current number of processed clauses  : 242
% 0.21/0.54  #    Positive orientable unit clauses  : 80
% 0.21/0.54  #    Positive unorientable unit clauses: 1
% 0.21/0.54  #    Negative unit clauses             : 0
% 0.21/0.54  #    Non-unit-clauses                  : 161
% 0.21/0.54  # Current number of unprocessed clauses: 4445
% 0.21/0.54  # ...number of literals in the above   : 12399
% 0.21/0.54  # Current number of archived formulas  : 0
% 0.21/0.54  # Current number of archived clauses   : 74
% 0.21/0.54  # Clause-clause subsumption calls (NU) : 3527
% 0.21/0.54  # Rec. Clause-clause subsumption calls : 3223
% 0.21/0.54  # Non-unit clause-clause subsumptions  : 509
% 0.21/0.54  # Unit Clause-clause subsumption calls : 63
% 0.21/0.54  # Rewrite failures with RHS unbound    : 0
% 0.21/0.54  # BW rewrite match attempts            : 416
% 0.21/0.54  # BW rewrite match successes           : 78
% 0.21/0.54  # Condensation attempts                : 0
% 0.21/0.54  # Condensation successes               : 0
% 0.21/0.54  # Termbank termtop insertions          : 163960
% 0.21/0.54  
% 0.21/0.54  # -------------------------------------------------
% 0.21/0.54  # User time                : 0.184 s
% 0.21/0.54  # System time              : 0.008 s
% 0.21/0.54  # Total time               : 0.192 s
% 0.21/0.54  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
