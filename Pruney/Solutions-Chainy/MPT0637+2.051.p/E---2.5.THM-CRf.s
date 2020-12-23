%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:31 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 (1157 expanded)
%              Number of clauses        :   56 ( 490 expanded)
%              Number of leaves         :   21 ( 333 expanded)
%              Depth                    :   16
%              Number of atoms          :  171 (1486 expanded)
%              Number of equality atoms :   71 ( 979 expanded)
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

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t124_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

fof(t127_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(k3_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t126_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(k2_relat_1(X1),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

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

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(c_0_21,plain,(
    ! [X31,X32] : k1_setfam_1(k2_tarski(X31,X32)) = k3_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_22,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X34)
      | v1_relat_1(k3_xboole_0(X34,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X22,X23,X24,X25] : k3_enumset1(X22,X22,X23,X24,X25) = k2_enumset1(X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X26,X27,X28,X29,X30] : k4_enumset1(X26,X26,X27,X28,X29,X30) = k3_enumset1(X26,X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_29,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_30,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k3_xboole_0(X13,X14)) = k4_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_31,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_38,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | k8_relat_1(X38,X39) = k3_xboole_0(X39,k2_zfmisc_1(k1_relat_1(X39),X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).

cnf(c_0_39,plain,
    ( v1_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_42,plain,
    ( k8_relat_1(X2,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_43,plain,(
    ! [X41,X42,X43] :
      ( ~ v1_relat_1(X43)
      | k8_relat_1(X41,k8_relat_1(X42,X43)) = k8_relat_1(k3_xboole_0(X41,X42),X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_relat_1])])).

cnf(c_0_44,plain,
    ( v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_40])).

cnf(c_0_46,plain,
    ( k8_relat_1(X2,X1) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_47,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(k3_xboole_0(X2,X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_48,plain,(
    ! [X50,X51] :
      ( ( r1_tarski(k5_relat_1(X51,k6_relat_1(X50)),X51)
        | ~ v1_relat_1(X51) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X50),X51),X51)
        | ~ v1_relat_1(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

fof(c_0_49,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | k8_relat_1(X36,X37) = k5_relat_1(X37,k6_relat_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_50,plain,(
    ! [X33] : v1_relat_1(k6_relat_1(X33)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_51,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))) = k8_relat_1(X2,X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_46,c_0_40])).

cnf(c_0_53,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)),X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_32]),c_0_33]),c_0_34]),c_0_35])).

fof(c_0_54,plain,(
    ! [X40] :
      ( ~ v1_relat_1(X40)
      | k8_relat_1(k2_relat_1(X40),X40) = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t126_relat_1])])).

fof(c_0_55,plain,(
    ! [X48] :
      ( k1_relat_1(k6_relat_1(X48)) = X48
      & k2_relat_1(k6_relat_1(X48)) = X48 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_56,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_57,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,plain,
    ( k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) = k8_relat_1(X1,k8_relat_1(X2,X3))
    | ~ v1_relat_1(X3) ),
    inference(rw,[status(thm)],[c_0_53,c_0_40])).

cnf(c_0_62,plain,
    ( k8_relat_1(k2_relat_1(X1),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,plain,
    ( r1_tarski(k8_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_59])])).

cnf(c_0_66,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_67,plain,
    ( v1_relat_1(k8_relat_1(X1,k8_relat_1(X2,X3)))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,plain,
    ( k8_relat_1(X1,k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_59])])).

fof(c_0_69,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(X53)
      | ~ r1_tarski(k1_relat_1(X53),X52)
      | k5_relat_1(k6_relat_1(X52),X53) = X53 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

fof(c_0_70,plain,(
    ! [X44,X45] :
      ( ( r1_tarski(k1_relat_1(X44),k1_relat_1(X45))
        | ~ r1_tarski(X44,X45)
        | ~ v1_relat_1(X45)
        | ~ v1_relat_1(X44) )
      & ( r1_tarski(k2_relat_1(X44),k2_relat_1(X45))
        | ~ r1_tarski(X44,X45)
        | ~ v1_relat_1(X45)
        | ~ v1_relat_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k6_relat_1(X2))
    | ~ r1_tarski(X1,k8_relat_1(X2,k6_relat_1(X3))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,plain,
    ( r1_tarski(k8_relat_1(X1,X2),X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_58])).

cnf(c_0_73,plain,
    ( v1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_59])])).

cnf(c_0_74,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_76,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( r1_tarski(k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X3))),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_78,plain,
    ( k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k6_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_68]),c_0_59])])).

fof(c_0_79,plain,(
    ! [X46,X47] :
      ( ~ v1_relat_1(X46)
      | ~ v1_relat_1(X47)
      | k4_relat_1(k5_relat_1(X46,X47)) = k5_relat_1(k4_relat_1(X47),k4_relat_1(X46)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_80,plain,(
    ! [X49] : k4_relat_1(k6_relat_1(X49)) = k6_relat_1(X49) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

fof(c_0_81,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

cnf(c_0_82,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_74]),c_0_59]),c_0_59]),c_0_75])])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_75]),c_0_59])])).

cnf(c_0_84,plain,
    ( r1_tarski(k6_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k6_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_85,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_86,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

fof(c_0_87,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_81])])])).

cnf(c_0_88,plain,
    ( k6_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X3)))
    | ~ r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_82]),c_0_59])])).

cnf(c_0_89,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_75]),c_0_59])])).

cnf(c_0_90,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X1))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_59])])).

cnf(c_0_91,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_92,plain,
    ( k6_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_68])).

cnf(c_0_93,plain,
    ( k4_relat_1(k8_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_58]),c_0_86]),c_0_59]),c_0_59])])).

cnf(c_0_94,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_95,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_92]),c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( k6_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_94,c_0_40])).

cnf(c_0_97,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k8_relat_1(X2,k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_95]),c_0_59])])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_92]),c_0_95]),c_0_97])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:58:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___107_C12_02_nc_F1_PI_AE_Q4_CS_SP_PS_S06DN
% 0.20/0.40  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.025 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.40  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.20/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.40  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.40  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.20/0.40  fof(t124_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 0.20/0.40  fof(t127_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(k3_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 0.20/0.40  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 0.20/0.40  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 0.20/0.40  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.20/0.40  fof(t126_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k8_relat_1(k2_relat_1(X1),X1)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 0.20/0.40  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.40  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.40  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 0.20/0.40  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.20/0.40  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 0.20/0.40  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 0.20/0.40  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 0.20/0.40  fof(c_0_21, plain, ![X31, X32]:k1_setfam_1(k2_tarski(X31,X32))=k3_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.40  fof(c_0_22, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.40  fof(c_0_23, plain, ![X34, X35]:(~v1_relat_1(X34)|v1_relat_1(k3_xboole_0(X34,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.20/0.40  cnf(c_0_24, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  fof(c_0_26, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.40  fof(c_0_27, plain, ![X22, X23, X24, X25]:k3_enumset1(X22,X22,X23,X24,X25)=k2_enumset1(X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.40  fof(c_0_28, plain, ![X26, X27, X28, X29, X30]:k4_enumset1(X26,X26,X27,X28,X29,X30)=k3_enumset1(X26,X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.40  fof(c_0_29, plain, ![X15, X16]:k4_xboole_0(X15,k4_xboole_0(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.40  fof(c_0_30, plain, ![X13, X14]:k4_xboole_0(X13,k3_xboole_0(X13,X14))=k4_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.20/0.40  cnf(c_0_31, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.40  cnf(c_0_32, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.40  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_35, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.40  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.40  cnf(c_0_37, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  fof(c_0_38, plain, ![X38, X39]:(~v1_relat_1(X39)|k8_relat_1(X38,X39)=k3_xboole_0(X39,k2_zfmisc_1(k1_relat_1(X39),X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).
% 0.20/0.40  cnf(c_0_39, plain, (v1_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.20/0.40  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.20/0.40  cnf(c_0_41, plain, (k4_xboole_0(X1,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.20/0.40  cnf(c_0_42, plain, (k8_relat_1(X2,X1)=k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.40  fof(c_0_43, plain, ![X41, X42, X43]:(~v1_relat_1(X43)|k8_relat_1(X41,k8_relat_1(X42,X43))=k8_relat_1(k3_xboole_0(X41,X42),X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_relat_1])])).
% 0.20/0.40  cnf(c_0_44, plain, (v1_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.40  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_40])).
% 0.20/0.40  cnf(c_0_46, plain, (k8_relat_1(X2,X1)=k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.20/0.40  cnf(c_0_47, plain, (k8_relat_1(X2,k8_relat_1(X3,X1))=k8_relat_1(k3_xboole_0(X2,X3),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.40  fof(c_0_48, plain, ![X50, X51]:((r1_tarski(k5_relat_1(X51,k6_relat_1(X50)),X51)|~v1_relat_1(X51))&(r1_tarski(k5_relat_1(k6_relat_1(X50),X51),X51)|~v1_relat_1(X51))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.20/0.40  fof(c_0_49, plain, ![X36, X37]:(~v1_relat_1(X37)|k8_relat_1(X36,X37)=k5_relat_1(X37,k6_relat_1(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.20/0.40  fof(c_0_50, plain, ![X33]:v1_relat_1(k6_relat_1(X33)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.20/0.40  cnf(c_0_51, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.40  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2)))=k8_relat_1(X2,X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_46, c_0_40])).
% 0.20/0.40  cnf(c_0_53, plain, (k8_relat_1(X2,k8_relat_1(X3,X1))=k8_relat_1(k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)),X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.20/0.40  fof(c_0_54, plain, ![X40]:(~v1_relat_1(X40)|k8_relat_1(k2_relat_1(X40),X40)=X40), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t126_relat_1])])).
% 0.20/0.40  fof(c_0_55, plain, ![X48]:(k1_relat_1(k6_relat_1(X48))=X48&k2_relat_1(k6_relat_1(X48))=X48), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.40  fof(c_0_56, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X11,X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.40  cnf(c_0_57, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.40  cnf(c_0_58, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.40  cnf(c_0_59, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.40  cnf(c_0_60, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.40  cnf(c_0_61, plain, (k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)=k8_relat_1(X1,k8_relat_1(X2,X3))|~v1_relat_1(X3)), inference(rw,[status(thm)],[c_0_53, c_0_40])).
% 0.20/0.40  cnf(c_0_62, plain, (k8_relat_1(k2_relat_1(X1),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.40  cnf(c_0_63, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.40  cnf(c_0_64, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.40  cnf(c_0_65, plain, (r1_tarski(k8_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_59])])).
% 0.20/0.40  cnf(c_0_66, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.40  cnf(c_0_67, plain, (v1_relat_1(k8_relat_1(X1,k8_relat_1(X2,X3)))|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.40  cnf(c_0_68, plain, (k8_relat_1(X1,k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_59])])).
% 0.20/0.40  fof(c_0_69, plain, ![X52, X53]:(~v1_relat_1(X53)|(~r1_tarski(k1_relat_1(X53),X52)|k5_relat_1(k6_relat_1(X52),X53)=X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.20/0.40  fof(c_0_70, plain, ![X44, X45]:((r1_tarski(k1_relat_1(X44),k1_relat_1(X45))|~r1_tarski(X44,X45)|~v1_relat_1(X45)|~v1_relat_1(X44))&(r1_tarski(k2_relat_1(X44),k2_relat_1(X45))|~r1_tarski(X44,X45)|~v1_relat_1(X45)|~v1_relat_1(X44))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.20/0.40  cnf(c_0_71, plain, (r1_tarski(X1,k6_relat_1(X2))|~r1_tarski(X1,k8_relat_1(X2,k6_relat_1(X3)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.40  cnf(c_0_72, plain, (r1_tarski(k8_relat_1(X1,X2),X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_66, c_0_58])).
% 0.20/0.40  cnf(c_0_73, plain, (v1_relat_1(k8_relat_1(X1,k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_59])])).
% 0.20/0.40  cnf(c_0_74, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.40  cnf(c_0_75, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.40  cnf(c_0_76, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.40  cnf(c_0_77, plain, (r1_tarski(k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X3))),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])])).
% 0.20/0.40  cnf(c_0_78, plain, (k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))))=k6_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_68]), c_0_59])])).
% 0.20/0.40  fof(c_0_79, plain, ![X46, X47]:(~v1_relat_1(X46)|(~v1_relat_1(X47)|k4_relat_1(k5_relat_1(X46,X47))=k5_relat_1(k4_relat_1(X47),k4_relat_1(X46)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.20/0.40  fof(c_0_80, plain, ![X49]:k4_relat_1(k6_relat_1(X49))=k6_relat_1(X49), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.20/0.40  fof(c_0_81, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.20/0.40  cnf(c_0_82, plain, (k8_relat_1(X1,k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_74]), c_0_59]), c_0_59]), c_0_75])])).
% 0.20/0.40  cnf(c_0_83, plain, (r1_tarski(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_75]), c_0_59])])).
% 0.20/0.40  cnf(c_0_84, plain, (r1_tarski(k6_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k6_relat_1(X2))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.40  cnf(c_0_85, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.40  cnf(c_0_86, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.40  fof(c_0_87, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_81])])])).
% 0.20/0.40  cnf(c_0_88, plain, (k6_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X3)))|~r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_82]), c_0_59])])).
% 0.20/0.40  cnf(c_0_89, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_75]), c_0_59])])).
% 0.20/0.40  cnf(c_0_90, plain, (k4_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k4_relat_1(X2),k6_relat_1(X1))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_59])])).
% 0.20/0.40  cnf(c_0_91, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.20/0.40  cnf(c_0_92, plain, (k6_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k8_relat_1(X1,k6_relat_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_68])).
% 0.20/0.40  cnf(c_0_93, plain, (k4_relat_1(k8_relat_1(X1,k6_relat_1(X2)))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_58]), c_0_86]), c_0_59]), c_0_59])])).
% 0.20/0.40  cnf(c_0_94, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.20/0.40  cnf(c_0_95, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k8_relat_1(X1,k6_relat_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_92]), c_0_93])).
% 0.20/0.40  cnf(c_0_96, negated_conjecture, (k6_relat_1(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_94, c_0_40])).
% 0.20/0.40  cnf(c_0_97, plain, (k8_relat_1(X1,k6_relat_1(X2))=k8_relat_1(X2,k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_95]), c_0_59])])).
% 0.20/0.40  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_92]), c_0_95]), c_0_97])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 99
% 0.20/0.40  # Proof object clause steps            : 56
% 0.20/0.40  # Proof object formula steps           : 43
% 0.20/0.40  # Proof object conjectures             : 7
% 0.20/0.40  # Proof object clause conjectures      : 4
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 23
% 0.20/0.40  # Proof object initial formulas used   : 21
% 0.20/0.40  # Proof object generating inferences   : 20
% 0.20/0.40  # Proof object simplifying inferences  : 66
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 23
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 28
% 0.20/0.40  # Removed in clause preprocessing      : 5
% 0.20/0.40  # Initial clauses in saturation        : 23
% 0.20/0.40  # Processed clauses                    : 296
% 0.20/0.40  # ...of these trivial                  : 23
% 0.20/0.40  # ...subsumed                          : 105
% 0.20/0.40  # ...remaining for further processing  : 167
% 0.20/0.40  # Other redundant clauses eliminated   : 2
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 2
% 0.20/0.40  # Backward-rewritten                   : 39
% 0.20/0.40  # Generated clauses                    : 1912
% 0.20/0.40  # ...of the previous two non-trivial   : 1406
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 1910
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
% 0.20/0.40  # Current number of processed clauses  : 102
% 0.20/0.40  #    Positive orientable unit clauses  : 35
% 0.20/0.40  #    Positive unorientable unit clauses: 1
% 0.20/0.40  #    Negative unit clauses             : 0
% 0.20/0.40  #    Non-unit-clauses                  : 66
% 0.20/0.40  # Current number of unprocessed clauses: 1148
% 0.20/0.40  # ...number of literals in the above   : 2613
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 68
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 688
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 631
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 106
% 0.20/0.40  # Unit Clause-clause subsumption calls : 7
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 73
% 0.20/0.40  # BW rewrite match successes           : 35
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 24149
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.047 s
% 0.20/0.40  # System time              : 0.007 s
% 0.20/0.40  # Total time               : 0.054 s
% 0.20/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
