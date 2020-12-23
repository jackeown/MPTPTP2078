%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:36 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 (6527 expanded)
%              Number of clauses        :   70 (2890 expanded)
%              Number of leaves         :   18 (1818 expanded)
%              Depth                    :   23
%              Number of atoms          :  185 (10516 expanded)
%              Number of equality atoms :   80 (4216 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t124_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

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

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(t139_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k8_relat_1(X1,k5_relat_1(X2,X3)) = k5_relat_1(X2,k8_relat_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

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

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(c_0_18,plain,(
    ! [X9,X10] : k1_setfam_1(k2_tarski(X9,X10)) = k3_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_19,plain,(
    ! [X4,X5] : k1_enumset1(X4,X4,X5) = k2_tarski(X4,X5) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | v1_relat_1(k3_xboole_0(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X6,X7,X8] : k2_enumset1(X6,X6,X7,X8) = k1_enumset1(X6,X7,X8) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | k8_relat_1(X18,X19) = k3_xboole_0(X19,k2_zfmisc_1(k1_relat_1(X19),X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).

fof(c_0_25,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | k8_relat_1(X16,X17) = k5_relat_1(X17,k6_relat_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_26,plain,(
    ! [X39] :
      ( v1_relat_1(k6_relat_1(X39))
      & v1_funct_1(k6_relat_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_27,plain,(
    ! [X32,X33] :
      ( ( r1_tarski(k5_relat_1(X33,k6_relat_1(X32)),X33)
        | ~ v1_relat_1(X33) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X32),X33),X33)
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

fof(c_0_28,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | k7_relat_1(X37,X36) = k5_relat_1(k6_relat_1(X36),X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_29,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k8_relat_1(X2,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X23,X24] :
      ( ( r1_tarski(k1_relat_1(X23),k1_relat_1(X24))
        | ~ r1_tarski(X23,X24)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) )
      & ( r1_tarski(k2_relat_1(X23),k2_relat_1(X24))
        | ~ r1_tarski(X23,X24)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_36,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,plain,(
    ! [X30] :
      ( k1_relat_1(k6_relat_1(X30)) = X30
      & k2_relat_1(k6_relat_1(X30)) = X30 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_39,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_40,plain,
    ( k8_relat_1(X2,X1) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_30]),c_0_31])).

cnf(c_0_41,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k8_relat_1(X2,k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_34]),c_0_34])])).

cnf(c_0_44,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_41])).

fof(c_0_47,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ r1_tarski(k2_relat_1(X35),X34)
      | k5_relat_1(X35,k6_relat_1(X34)) = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

cnf(c_0_48,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2)
    | ~ v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_34])])).

cnf(c_0_49,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_34])])).

fof(c_0_50,plain,(
    ! [X20,X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | k8_relat_1(X20,k5_relat_1(X21,X22)) = k5_relat_1(X21,k8_relat_1(X20,X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_relat_1])])])).

fof(c_0_51,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ v1_relat_1(X26)
      | k4_relat_1(k5_relat_1(X25,X26)) = k5_relat_1(k4_relat_1(X26),k4_relat_1(X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_52,plain,(
    ! [X31] : k4_relat_1(k6_relat_1(X31)) = k6_relat_1(X31) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

cnf(c_0_53,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_55,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3)) = k8_relat_1(X3,k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_49])).

cnf(c_0_56,plain,
    ( k8_relat_1(X3,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X1)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_49])]),c_0_55])).

cnf(c_0_60,plain,
    ( k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,X3)) = k8_relat_1(X2,k5_relat_1(k6_relat_1(X1),X3))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_56,c_0_34])).

cnf(c_0_61,plain,
    ( k4_relat_1(k8_relat_1(X1,X2)) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_33]),c_0_58]),c_0_34])])).

cnf(c_0_62,plain,
    ( k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X1))) = k8_relat_1(X2,k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_46])).

cnf(c_0_63,plain,
    ( k4_relat_1(k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X2,k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_41]),c_0_58]),c_0_58]),c_0_41]),c_0_34]),c_0_34])])).

cnf(c_0_64,plain,
    ( k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,k6_relat_1(X3))) = k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_34]),c_0_41])).

cnf(c_0_65,plain,
    ( v1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_46])).

cnf(c_0_66,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k8_relat_1(X2,k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_63]),c_0_64]),c_0_62]),c_0_65])])).

fof(c_0_67,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X15)
      | k7_relat_1(k7_relat_1(X15,X13),X14) = k7_relat_1(X15,k3_xboole_0(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_68,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k8_relat_1(X2,k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_46])).

cnf(c_0_69,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_66])).

cnf(c_0_70,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_71,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_30]),c_0_31])).

cnf(c_0_73,plain,
    ( k4_relat_1(k7_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X1),k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_37]),c_0_58]),c_0_34])])).

cnf(c_0_74,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_34])])).

cnf(c_0_75,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_76,plain,(
    ! [X38] :
      ( ~ v1_relat_1(X38)
      | k7_relat_1(X38,k1_relat_1(X38)) = X38 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_77,plain,
    ( k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_68]),c_0_69]),c_0_55]),c_0_49])])).

cnf(c_0_78,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_37])).

cnf(c_0_79,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_80,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_81,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X2) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[c_0_59,c_0_77])).

cnf(c_0_82,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_34])).

cnf(c_0_83,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_34]),c_0_80])).

cnf(c_0_84,plain,
    ( k7_relat_1(k6_relat_1(X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_81]),c_0_34])])).

cnf(c_0_85,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[c_0_46,c_0_69])).

fof(c_0_86,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

cnf(c_0_87,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_72]),c_0_34])])).

cnf(c_0_88,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X1))) = k6_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85]),c_0_84]),c_0_83])).

fof(c_0_89,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_86])])])).

cnf(c_0_90,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),k6_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_85])).

cnf(c_0_91,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_88]),c_0_80])).

cnf(c_0_92,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_93,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_72]),c_0_34])])).

cnf(c_0_94,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_30]),c_0_31])).

cnf(c_0_96,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_44]),c_0_41]),c_0_34])])).

cnf(c_0_97,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_98,plain,
    ( r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_83])).

cnf(c_0_99,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) != k8_relat_1(esk1_0,k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_95,c_0_41])).

cnf(c_0_101,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_96,c_0_69])).

cnf(c_0_102,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_80]),c_0_80]),c_0_34]),c_0_34])])).

cnf(c_0_103,plain,
    ( k7_relat_1(k6_relat_1(X1),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_83]),c_0_34])])).

cnf(c_0_104,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) != k7_relat_1(k6_relat_1(esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_100,c_0_69])).

cnf(c_0_105,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_85]),c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_105]),c_0_85])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:34:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.51  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 0.20/0.51  # and selection function SelectNewComplexAHP.
% 0.20/0.51  #
% 0.20/0.51  # Preprocessing time       : 0.027 s
% 0.20/0.51  
% 0.20/0.51  # Proof found!
% 0.20/0.51  # SZS status Theorem
% 0.20/0.51  # SZS output start CNFRefutation
% 0.20/0.51  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.51  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.51  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.20/0.51  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.51  fof(t124_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 0.20/0.51  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 0.20/0.51  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.20/0.51  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 0.20/0.51  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.20/0.51  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.20/0.51  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.51  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 0.20/0.51  fof(t139_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k8_relat_1(X1,k5_relat_1(X2,X3))=k5_relat_1(X2,k8_relat_1(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_relat_1)).
% 0.20/0.51  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 0.20/0.51  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 0.20/0.51  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 0.20/0.51  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.20/0.51  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 0.20/0.51  fof(c_0_18, plain, ![X9, X10]:k1_setfam_1(k2_tarski(X9,X10))=k3_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.51  fof(c_0_19, plain, ![X4, X5]:k1_enumset1(X4,X4,X5)=k2_tarski(X4,X5), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.51  fof(c_0_20, plain, ![X11, X12]:(~v1_relat_1(X11)|v1_relat_1(k3_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.20/0.51  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.51  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.51  fof(c_0_23, plain, ![X6, X7, X8]:k2_enumset1(X6,X6,X7,X8)=k1_enumset1(X6,X7,X8), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.51  fof(c_0_24, plain, ![X18, X19]:(~v1_relat_1(X19)|k8_relat_1(X18,X19)=k3_xboole_0(X19,k2_zfmisc_1(k1_relat_1(X19),X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).
% 0.20/0.51  fof(c_0_25, plain, ![X16, X17]:(~v1_relat_1(X17)|k8_relat_1(X16,X17)=k5_relat_1(X17,k6_relat_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.20/0.51  fof(c_0_26, plain, ![X39]:(v1_relat_1(k6_relat_1(X39))&v1_funct_1(k6_relat_1(X39))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.20/0.51  fof(c_0_27, plain, ![X32, X33]:((r1_tarski(k5_relat_1(X33,k6_relat_1(X32)),X33)|~v1_relat_1(X33))&(r1_tarski(k5_relat_1(k6_relat_1(X32),X33),X33)|~v1_relat_1(X33))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.20/0.51  fof(c_0_28, plain, ![X36, X37]:(~v1_relat_1(X37)|k7_relat_1(X37,X36)=k5_relat_1(k6_relat_1(X36),X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.20/0.51  cnf(c_0_29, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.51  cnf(c_0_30, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.51  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.51  cnf(c_0_32, plain, (k8_relat_1(X2,X1)=k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.51  cnf(c_0_33, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.51  cnf(c_0_34, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.51  fof(c_0_35, plain, ![X23, X24]:((r1_tarski(k1_relat_1(X23),k1_relat_1(X24))|~r1_tarski(X23,X24)|~v1_relat_1(X24)|~v1_relat_1(X23))&(r1_tarski(k2_relat_1(X23),k2_relat_1(X24))|~r1_tarski(X23,X24)|~v1_relat_1(X24)|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.20/0.51  cnf(c_0_36, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.51  cnf(c_0_37, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.51  fof(c_0_38, plain, ![X30]:(k1_relat_1(k6_relat_1(X30))=X30&k2_relat_1(k6_relat_1(X30))=X30), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.51  cnf(c_0_39, plain, (v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.20/0.51  cnf(c_0_40, plain, (k8_relat_1(X2,X1)=k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_30]), c_0_31])).
% 0.20/0.51  cnf(c_0_41, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k8_relat_1(X2,k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.51  cnf(c_0_42, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.51  cnf(c_0_43, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_34]), c_0_34])])).
% 0.20/0.51  cnf(c_0_44, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.51  cnf(c_0_45, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.51  cnf(c_0_46, plain, (k8_relat_1(X1,k6_relat_1(X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_41])).
% 0.20/0.51  fof(c_0_47, plain, ![X34, X35]:(~v1_relat_1(X35)|(~r1_tarski(k2_relat_1(X35),X34)|k5_relat_1(X35,k6_relat_1(X34))=X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.20/0.51  cnf(c_0_48, plain, (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2)|~v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_34])])).
% 0.20/0.51  cnf(c_0_49, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_34])])).
% 0.20/0.51  fof(c_0_50, plain, ![X20, X21, X22]:(~v1_relat_1(X21)|(~v1_relat_1(X22)|k8_relat_1(X20,k5_relat_1(X21,X22))=k5_relat_1(X21,k8_relat_1(X20,X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_relat_1])])])).
% 0.20/0.51  fof(c_0_51, plain, ![X25, X26]:(~v1_relat_1(X25)|(~v1_relat_1(X26)|k4_relat_1(k5_relat_1(X25,X26))=k5_relat_1(k4_relat_1(X26),k4_relat_1(X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.20/0.51  fof(c_0_52, plain, ![X31]:k4_relat_1(k6_relat_1(X31))=k6_relat_1(X31), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.20/0.51  cnf(c_0_53, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.51  cnf(c_0_54, plain, (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49])])).
% 0.20/0.51  cnf(c_0_55, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X3))=k8_relat_1(X3,k7_relat_1(k6_relat_1(X1),X2))), inference(spm,[status(thm)],[c_0_33, c_0_49])).
% 0.20/0.51  cnf(c_0_56, plain, (k8_relat_1(X3,k5_relat_1(X1,X2))=k5_relat_1(X1,k8_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.51  cnf(c_0_57, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.51  cnf(c_0_58, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.51  cnf(c_0_59, plain, (k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X1))=k7_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_49])]), c_0_55])).
% 0.20/0.51  cnf(c_0_60, plain, (k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,X3))=k8_relat_1(X2,k5_relat_1(k6_relat_1(X1),X3))|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_56, c_0_34])).
% 0.20/0.51  cnf(c_0_61, plain, (k4_relat_1(k8_relat_1(X1,X2))=k5_relat_1(k6_relat_1(X1),k4_relat_1(X2))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_33]), c_0_58]), c_0_34])])).
% 0.20/0.51  cnf(c_0_62, plain, (k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X1)))=k8_relat_1(X2,k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_46])).
% 0.20/0.51  cnf(c_0_63, plain, (k4_relat_1(k8_relat_1(X1,k6_relat_1(X2)))=k8_relat_1(X2,k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_41]), c_0_58]), c_0_58]), c_0_41]), c_0_34]), c_0_34])])).
% 0.20/0.51  cnf(c_0_64, plain, (k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,k6_relat_1(X3)))=k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_34]), c_0_41])).
% 0.20/0.51  cnf(c_0_65, plain, (v1_relat_1(k8_relat_1(X1,k6_relat_1(X2)))), inference(spm,[status(thm)],[c_0_49, c_0_46])).
% 0.20/0.51  cnf(c_0_66, plain, (k8_relat_1(X1,k6_relat_1(X2))=k8_relat_1(X2,k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_63]), c_0_64]), c_0_62]), c_0_65])])).
% 0.20/0.51  fof(c_0_67, plain, ![X13, X14, X15]:(~v1_relat_1(X15)|k7_relat_1(k7_relat_1(X15,X13),X14)=k7_relat_1(X15,k3_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.20/0.51  cnf(c_0_68, plain, (k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k8_relat_1(X2,k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_63, c_0_46])).
% 0.20/0.51  cnf(c_0_69, plain, (k8_relat_1(X1,k6_relat_1(X2))=k7_relat_1(k6_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_46, c_0_66])).
% 0.20/0.51  cnf(c_0_70, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.51  cnf(c_0_71, plain, (k4_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.51  cnf(c_0_72, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_30]), c_0_31])).
% 0.20/0.51  cnf(c_0_73, plain, (k4_relat_1(k7_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X1),k6_relat_1(X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_37]), c_0_58]), c_0_34])])).
% 0.20/0.51  cnf(c_0_74, plain, (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3))=k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_34])])).
% 0.20/0.51  cnf(c_0_75, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.51  fof(c_0_76, plain, ![X38]:(~v1_relat_1(X38)|k7_relat_1(X38,k1_relat_1(X38))=X38), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.20/0.51  cnf(c_0_77, plain, (k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3))=k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_68]), c_0_69]), c_0_55]), c_0_49])])).
% 0.20/0.51  cnf(c_0_78, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_75, c_0_37])).
% 0.20/0.51  cnf(c_0_79, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.51  cnf(c_0_80, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.51  cnf(c_0_81, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X2)=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[c_0_59, c_0_77])).
% 0.20/0.51  cnf(c_0_82, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_78, c_0_34])).
% 0.20/0.51  cnf(c_0_83, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_34]), c_0_80])).
% 0.20/0.51  cnf(c_0_84, plain, (k7_relat_1(k6_relat_1(X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_81]), c_0_34])])).
% 0.20/0.51  cnf(c_0_85, plain, (k7_relat_1(k6_relat_1(X1),X2)=k7_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[c_0_46, c_0_69])).
% 0.20/0.51  fof(c_0_86, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.20/0.51  cnf(c_0_87, plain, (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_72]), c_0_34])])).
% 0.20/0.51  cnf(c_0_88, plain, (k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))=k6_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85]), c_0_84]), c_0_83])).
% 0.20/0.51  fof(c_0_89, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_86])])])).
% 0.20/0.51  cnf(c_0_90, plain, (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),k6_relat_1(X2))), inference(spm,[status(thm)],[c_0_87, c_0_85])).
% 0.20/0.51  cnf(c_0_91, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_88]), c_0_80])).
% 0.20/0.51  cnf(c_0_92, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.51  cnf(c_0_93, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_72]), c_0_34])])).
% 0.20/0.51  cnf(c_0_94, plain, (k7_relat_1(k7_relat_1(X1,X2),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_72, c_0_91])).
% 0.20/0.51  cnf(c_0_95, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_30]), c_0_31])).
% 0.20/0.51  cnf(c_0_96, plain, (k8_relat_1(X1,k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_44]), c_0_41]), c_0_34])])).
% 0.20/0.51  cnf(c_0_97, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.51  cnf(c_0_98, plain, (r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_93, c_0_83])).
% 0.20/0.51  cnf(c_0_99, plain, (k7_relat_1(k7_relat_1(X1,X2),k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))=k7_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_72, c_0_94])).
% 0.20/0.51  cnf(c_0_100, negated_conjecture, (k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))!=k8_relat_1(esk1_0,k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_95, c_0_41])).
% 0.20/0.51  cnf(c_0_101, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_96, c_0_69])).
% 0.20/0.51  cnf(c_0_102, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_80]), c_0_80]), c_0_34]), c_0_34])])).
% 0.20/0.51  cnf(c_0_103, plain, (k7_relat_1(k6_relat_1(X1),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_83]), c_0_34])])).
% 0.20/0.51  cnf(c_0_104, negated_conjecture, (k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))!=k7_relat_1(k6_relat_1(esk2_0),esk1_0)), inference(rw,[status(thm)],[c_0_100, c_0_69])).
% 0.20/0.51  cnf(c_0_105, plain, (k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_85]), c_0_103])).
% 0.20/0.51  cnf(c_0_106, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_105]), c_0_85])]), ['proof']).
% 0.20/0.51  # SZS output end CNFRefutation
% 0.20/0.51  # Proof object total steps             : 107
% 0.20/0.51  # Proof object clause steps            : 70
% 0.20/0.51  # Proof object formula steps           : 37
% 0.20/0.51  # Proof object conjectures             : 8
% 0.20/0.51  # Proof object clause conjectures      : 5
% 0.20/0.51  # Proof object formula conjectures     : 3
% 0.20/0.51  # Proof object initial clauses used    : 21
% 0.20/0.51  # Proof object initial formulas used   : 18
% 0.20/0.51  # Proof object generating inferences   : 36
% 0.20/0.51  # Proof object simplifying inferences  : 81
% 0.20/0.51  # Training examples: 0 positive, 0 negative
% 0.20/0.51  # Parsed axioms                        : 19
% 0.20/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.51  # Initial clauses                      : 23
% 0.20/0.51  # Removed in clause preprocessing      : 3
% 0.20/0.51  # Initial clauses in saturation        : 20
% 0.20/0.51  # Processed clauses                    : 1061
% 0.20/0.51  # ...of these trivial                  : 272
% 0.20/0.51  # ...subsumed                          : 366
% 0.20/0.51  # ...remaining for further processing  : 423
% 0.20/0.51  # Other redundant clauses eliminated   : 0
% 0.20/0.51  # Clauses deleted for lack of memory   : 0
% 0.20/0.51  # Backward-subsumed                    : 30
% 0.20/0.51  # Backward-rewritten                   : 61
% 0.20/0.51  # Generated clauses                    : 12139
% 0.20/0.51  # ...of the previous two non-trivial   : 9605
% 0.20/0.51  # Contextual simplify-reflections      : 0
% 0.20/0.51  # Paramodulations                      : 12139
% 0.20/0.51  # Factorizations                       : 0
% 0.20/0.51  # Equation resolutions                 : 0
% 0.20/0.51  # Propositional unsat checks           : 0
% 0.20/0.51  #    Propositional check models        : 0
% 0.20/0.51  #    Propositional check unsatisfiable : 0
% 0.20/0.51  #    Propositional clauses             : 0
% 0.20/0.51  #    Propositional clauses after purity: 0
% 0.20/0.51  #    Propositional unsat core size     : 0
% 0.20/0.51  #    Propositional preprocessing time  : 0.000
% 0.20/0.51  #    Propositional encoding time       : 0.000
% 0.20/0.51  #    Propositional solver time         : 0.000
% 0.20/0.51  #    Success case prop preproc time    : 0.000
% 0.20/0.51  #    Success case prop encoding time   : 0.000
% 0.20/0.51  #    Success case prop solver time     : 0.000
% 0.20/0.51  # Current number of processed clauses  : 332
% 0.20/0.51  #    Positive orientable unit clauses  : 113
% 0.20/0.51  #    Positive unorientable unit clauses: 7
% 0.20/0.51  #    Negative unit clauses             : 0
% 0.20/0.51  #    Non-unit-clauses                  : 212
% 0.20/0.51  # Current number of unprocessed clauses: 8205
% 0.20/0.51  # ...number of literals in the above   : 16422
% 0.20/0.51  # Current number of archived formulas  : 0
% 0.20/0.51  # Current number of archived clauses   : 94
% 0.20/0.51  # Clause-clause subsumption calls (NU) : 2904
% 0.20/0.51  # Rec. Clause-clause subsumption calls : 2739
% 0.20/0.51  # Non-unit clause-clause subsumptions  : 352
% 0.20/0.51  # Unit Clause-clause subsumption calls : 104
% 0.20/0.51  # Rewrite failures with RHS unbound    : 0
% 0.20/0.51  # BW rewrite match attempts            : 488
% 0.20/0.51  # BW rewrite match successes           : 181
% 0.20/0.51  # Condensation attempts                : 0
% 0.20/0.51  # Condensation successes               : 0
% 0.20/0.51  # Termbank termtop insertions          : 187003
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.149 s
% 0.20/0.51  # System time              : 0.016 s
% 0.20/0.51  # Total time               : 0.165 s
% 0.20/0.51  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
