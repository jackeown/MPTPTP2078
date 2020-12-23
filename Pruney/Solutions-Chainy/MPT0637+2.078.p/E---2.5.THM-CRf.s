%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:35 EST 2020

% Result     : Theorem 0.99s
% Output     : CNFRefutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  135 (14359 expanded)
%              Number of clauses        :   94 (6206 expanded)
%              Number of leaves         :   20 (4076 expanded)
%              Depth                    :   19
%              Number of atoms          :  261 (21689 expanded)
%              Number of equality atoms :  104 (11214 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    7 (   2 average)

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

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t124_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

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

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(c_0_20,plain,(
    ! [X11,X12] : k1_setfam_1(k2_tarski(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_21,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | k1_relat_1(k7_relat_1(X36,X35)) = k3_xboole_0(k1_relat_1(X36),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

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
    ! [X34] :
      ( ~ v1_relat_1(X34)
      | k5_relat_1(X34,k6_relat_1(k2_relat_1(X34))) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_27,plain,(
    ! [X30] :
      ( k1_relat_1(k6_relat_1(X30)) = X30
      & k2_relat_1(k6_relat_1(X30)) = X30 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_28,plain,(
    ! [X13] : v1_relat_1(k6_relat_1(X13)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_29,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | k8_relat_1(X21,X22) = k3_xboole_0(X22,k2_zfmisc_1(k1_relat_1(X22),X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).

cnf(c_0_30,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | k7_relat_1(k5_relat_1(X17,X18),X16) = k5_relat_1(k7_relat_1(X17,X16),X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

cnf(c_0_34,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | k7_relat_1(X38,X37) = k5_relat_1(k6_relat_1(X37),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_38,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | v1_relat_1(k3_xboole_0(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

cnf(c_0_39,plain,
    ( k8_relat_1(X2,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_41,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_44,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k8_relat_1(X2,X1) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_31]),c_0_32])).

cnf(c_0_47,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_36])])).

cnf(c_0_48,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_36])])).

cnf(c_0_49,plain,
    ( k5_relat_1(k7_relat_1(X1,X2),X3) = k5_relat_1(k6_relat_1(X2),k5_relat_1(X1,X3))
    | ~ v1_relat_1(k5_relat_1(X1,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_42])).

fof(c_0_50,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ v1_relat_1(X26)
      | k4_relat_1(k5_relat_1(X25,X26)) = k5_relat_1(k4_relat_1(X26),k4_relat_1(X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_51,plain,(
    ! [X31] : k4_relat_1(k6_relat_1(X31)) = k6_relat_1(X31) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

fof(c_0_52,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r1_tarski(k2_relat_1(X33),X32)
      | k5_relat_1(X33,k6_relat_1(X32)) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

fof(c_0_53,plain,(
    ! [X4,X5] : r1_tarski(k3_xboole_0(X4,X5),X4) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_54,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_31]),c_0_32])).

cnf(c_0_55,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(X1),X2))) = k8_relat_1(X2,X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_43]),c_0_43]),c_0_36]),c_0_36])])).

cnf(c_0_57,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_61,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X27)
      | ~ v1_relat_1(X28)
      | ~ v1_relat_1(X29)
      | k5_relat_1(k5_relat_1(X27,X28),X29) = k5_relat_1(X27,k5_relat_1(X28,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_62,plain,
    ( v1_relat_1(k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_40])).

cnf(c_0_63,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(k2_zfmisc_1(k1_relat_1(X1),X2)),k6_relat_1(X1))) = k8_relat_1(X2,X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k4_relat_1(X2),k6_relat_1(X1))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_36])])).

cnf(c_0_65,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_35]),c_0_36])])).

fof(c_0_66,plain,(
    ! [X39] :
      ( ~ v1_relat_1(X39)
      | k7_relat_1(X39,k1_relat_1(X39)) = X39 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_67,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_31]),c_0_32])).

cnf(c_0_68,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( v1_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)))
    | ~ v1_relat_1(k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_44])).

cnf(c_0_70,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(k2_zfmisc_1(X1,X2)),k6_relat_1(k6_relat_1(X1)))) = k8_relat_1(X2,k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_41]),c_0_36])])).

fof(c_0_71,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | k8_relat_1(X19,X20) = k5_relat_1(X20,k6_relat_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

cnf(c_0_72,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X1)),X2)) = k1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_40,c_0_47])).

cnf(c_0_73,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_58]),c_0_58]),c_0_36])])).

cnf(c_0_74,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_75,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_40])).

cnf(c_0_76,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k6_relat_1(X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_43]),c_0_36])])).

cnf(c_0_77,plain,
    ( v1_relat_1(k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_41]),c_0_36]),c_0_36])])).

cnf(c_0_78,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_79,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(X2)))) = k1_relat_1(k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_56])).

cnf(c_0_80,plain,
    ( r1_tarski(k8_relat_1(X1,X2),X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_46])).

cnf(c_0_81,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),X3)) = k5_relat_1(k6_relat_1(X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_73]),c_0_36]),c_0_36])])).

cnf(c_0_82,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_74])).

cnf(c_0_83,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_41]),c_0_36])])).

cnf(c_0_84,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k5_relat_1(k6_relat_1(X1),X2),X3)) = k5_relat_1(k5_relat_1(k6_relat_1(X1),X2),X3)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_76]),c_0_36])])).

cnf(c_0_85,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_44]),c_0_36])])).

cnf(c_0_86,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_36])])).

cnf(c_0_87,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_65]),c_0_41])).

cnf(c_0_88,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_78])).

cnf(c_0_89,plain,
    ( k5_relat_1(k6_relat_1(X1),X2) = X2
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_90,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_44]),c_0_36])])).

cnf(c_0_91,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_73]),c_0_41])).

cnf(c_0_92,plain,
    ( k7_relat_1(k5_relat_1(X1,k5_relat_1(X2,X3)),X4) = k5_relat_1(k7_relat_1(k5_relat_1(X1,X2),X4),X3)
    | ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_68])).

cnf(c_0_93,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_36])])).

cnf(c_0_94,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_41]),c_0_56]),c_0_36])])).

cnf(c_0_95,plain,
    ( r1_tarski(k5_relat_1(X1,k5_relat_1(X2,k6_relat_1(X3))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_68]),c_0_36])])).

cnf(c_0_96,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_86])])).

fof(c_0_97,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ v1_relat_1(X24)
      | r1_tarski(k2_relat_1(k5_relat_1(X23,X24)),k2_relat_1(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

cnf(c_0_98,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_41]),c_0_56]),c_0_36])])).

cnf(c_0_99,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3) = k5_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X1)),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_43]),c_0_56]),c_0_43]),c_0_36]),c_0_36]),c_0_36])])).

cnf(c_0_100,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_73]),c_0_41])).

cnf(c_0_101,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_86]),c_0_36]),c_0_36])])).

cnf(c_0_102,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

fof(c_0_103,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

cnf(c_0_104,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_65]),c_0_36]),c_0_36])]),c_0_56]),c_0_56])).

cnf(c_0_105,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3)) = X2
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_98]),c_0_86])])).

cnf(c_0_106,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3)) = k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_99]),c_0_86])])).

cnf(c_0_107,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_101])])).

cnf(c_0_108,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,k5_relat_1(X2,X3))),k2_relat_1(X3))
    | ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_68])).

fof(c_0_109,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_103])])])).

cnf(c_0_110,plain,
    ( k5_relat_1(k7_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2))),X2) = k5_relat_1(X1,X2)
    | ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_42])).

cnf(c_0_111,plain,
    ( k5_relat_1(k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3),k6_relat_1(X2)) = k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_85]),c_0_36])]),c_0_86])])).

cnf(c_0_112,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_104,c_0_65])).

cnf(c_0_113,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X1,X2))),k2_relat_1(k4_relat_1(X1)))
    | ~ v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_57])).

cnf(c_0_114,plain,
    ( k4_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_36])])).

cnf(c_0_115,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))) = X3
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_99]),c_0_106])).

cnf(c_0_116,plain,
    ( k5_relat_1(X1,k5_relat_1(X2,k6_relat_1(k2_relat_1(k5_relat_1(X1,X2))))) = k5_relat_1(X1,X2)
    | ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_68]),c_0_36])])).

cnf(c_0_117,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_107]),c_0_35]),c_0_36]),c_0_36])])).

cnf(c_0_118,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_93]),c_0_35]),c_0_43]),c_0_36]),c_0_36]),c_0_36])])).

cnf(c_0_119,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_120,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_85]),c_0_36])]),c_0_111]),c_0_86])])).

cnf(c_0_121,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X1)
    | ~ r1_tarski(X1,k1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X2)))) ),
    inference(spm,[status(thm)],[c_0_112,c_0_90])).

cnf(c_0_122,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(X1)),k1_relat_1(X1))
    | ~ v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_82]),c_0_58]),c_0_35]),c_0_58]),c_0_36]),c_0_36])])).

cnf(c_0_123,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_107]),c_0_58]),c_0_36])])).

cnf(c_0_124,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117]),c_0_118]),c_0_86]),c_0_36]),c_0_36])])).

cnf(c_0_125,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_31]),c_0_32])).

cnf(c_0_126,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_99]),c_0_107]),c_0_106]),c_0_107])).

cnf(c_0_127,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))))) = k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_123]),c_0_124]),c_0_107]),c_0_123]),c_0_124]),c_0_123]),c_0_86]),c_0_86])])).

cnf(c_0_128,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)),k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_44])).

cnf(c_0_129,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),esk2_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_125,c_0_47])).

cnf(c_0_130,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_131,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_107]),c_0_41]),c_0_36])])).

cnf(c_0_132,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_44]),c_0_36])])).

cnf(c_0_133,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_130]),c_0_131])])).

cnf(c_0_134,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_133])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:15:10 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.99/1.17  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.99/1.17  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.99/1.17  #
% 0.99/1.17  # Preprocessing time       : 0.027 s
% 0.99/1.17  # Presaturation interreduction done
% 0.99/1.17  
% 0.99/1.17  # Proof found!
% 0.99/1.17  # SZS status Theorem
% 0.99/1.17  # SZS output start CNFRefutation
% 0.99/1.17  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.99/1.17  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.99/1.17  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.99/1.17  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.99/1.17  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 0.99/1.17  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.99/1.17  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.99/1.17  fof(t124_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 0.99/1.17  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 0.99/1.17  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.99/1.17  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.99/1.17  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 0.99/1.17  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 0.99/1.17  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 0.99/1.17  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.99/1.17  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 0.99/1.17  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.99/1.17  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 0.99/1.17  fof(t45_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 0.99/1.17  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 0.99/1.17  fof(c_0_20, plain, ![X11, X12]:k1_setfam_1(k2_tarski(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.99/1.17  fof(c_0_21, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.99/1.17  fof(c_0_22, plain, ![X35, X36]:(~v1_relat_1(X36)|k1_relat_1(k7_relat_1(X36,X35))=k3_xboole_0(k1_relat_1(X36),X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.99/1.17  cnf(c_0_23, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.99/1.17  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.99/1.17  fof(c_0_25, plain, ![X8, X9, X10]:k2_enumset1(X8,X8,X9,X10)=k1_enumset1(X8,X9,X10), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.99/1.17  fof(c_0_26, plain, ![X34]:(~v1_relat_1(X34)|k5_relat_1(X34,k6_relat_1(k2_relat_1(X34)))=X34), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.99/1.17  fof(c_0_27, plain, ![X30]:(k1_relat_1(k6_relat_1(X30))=X30&k2_relat_1(k6_relat_1(X30))=X30), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.99/1.17  fof(c_0_28, plain, ![X13]:v1_relat_1(k6_relat_1(X13)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.99/1.17  fof(c_0_29, plain, ![X21, X22]:(~v1_relat_1(X22)|k8_relat_1(X21,X22)=k3_xboole_0(X22,k2_zfmisc_1(k1_relat_1(X22),X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).
% 0.99/1.17  cnf(c_0_30, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.99/1.17  cnf(c_0_31, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.99/1.17  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.99/1.17  fof(c_0_33, plain, ![X16, X17, X18]:(~v1_relat_1(X17)|(~v1_relat_1(X18)|k7_relat_1(k5_relat_1(X17,X18),X16)=k5_relat_1(k7_relat_1(X17,X16),X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 0.99/1.17  cnf(c_0_34, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.99/1.17  cnf(c_0_35, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.99/1.17  cnf(c_0_36, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.99/1.17  fof(c_0_37, plain, ![X37, X38]:(~v1_relat_1(X38)|k7_relat_1(X38,X37)=k5_relat_1(k6_relat_1(X37),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.99/1.17  fof(c_0_38, plain, ![X14, X15]:(~v1_relat_1(X14)|v1_relat_1(k3_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.99/1.17  cnf(c_0_39, plain, (k8_relat_1(X2,X1)=k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.99/1.17  cnf(c_0_40, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.99/1.17  cnf(c_0_41, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.99/1.17  cnf(c_0_42, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.99/1.17  cnf(c_0_43, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.99/1.17  cnf(c_0_44, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.99/1.17  cnf(c_0_45, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.99/1.17  cnf(c_0_46, plain, (k8_relat_1(X2,X1)=k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_31]), c_0_32])).
% 0.99/1.17  cnf(c_0_47, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_36])])).
% 0.99/1.17  cnf(c_0_48, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_36])])).
% 0.99/1.17  cnf(c_0_49, plain, (k5_relat_1(k7_relat_1(X1,X2),X3)=k5_relat_1(k6_relat_1(X2),k5_relat_1(X1,X3))|~v1_relat_1(k5_relat_1(X1,X3))|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_42])).
% 0.99/1.17  fof(c_0_50, plain, ![X25, X26]:(~v1_relat_1(X25)|(~v1_relat_1(X26)|k4_relat_1(k5_relat_1(X25,X26))=k5_relat_1(k4_relat_1(X26),k4_relat_1(X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.99/1.17  fof(c_0_51, plain, ![X31]:k4_relat_1(k6_relat_1(X31))=k6_relat_1(X31), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.99/1.17  fof(c_0_52, plain, ![X32, X33]:(~v1_relat_1(X33)|(~r1_tarski(k2_relat_1(X33),X32)|k5_relat_1(X33,k6_relat_1(X32))=X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.99/1.17  fof(c_0_53, plain, ![X4, X5]:r1_tarski(k3_xboole_0(X4,X5),X4), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.99/1.17  cnf(c_0_54, plain, (v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_31]), c_0_32])).
% 0.99/1.17  cnf(c_0_55, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(X1),X2)))=k8_relat_1(X2,X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.99/1.17  cnf(c_0_56, plain, (k7_relat_1(k6_relat_1(X1),X2)=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_43]), c_0_43]), c_0_36]), c_0_36])])).
% 0.99/1.17  cnf(c_0_57, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.99/1.17  cnf(c_0_58, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.99/1.17  cnf(c_0_59, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.99/1.17  cnf(c_0_60, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.99/1.17  fof(c_0_61, plain, ![X27, X28, X29]:(~v1_relat_1(X27)|(~v1_relat_1(X28)|(~v1_relat_1(X29)|k5_relat_1(k5_relat_1(X27,X28),X29)=k5_relat_1(X27,k5_relat_1(X28,X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.99/1.17  cnf(c_0_62, plain, (v1_relat_1(k1_relat_1(k7_relat_1(X1,X2)))|~v1_relat_1(k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_54, c_0_40])).
% 0.99/1.17  cnf(c_0_63, plain, (k1_relat_1(k5_relat_1(k6_relat_1(k2_zfmisc_1(k1_relat_1(X1),X2)),k6_relat_1(X1)))=k8_relat_1(X2,X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.99/1.17  cnf(c_0_64, plain, (k4_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k4_relat_1(X2),k6_relat_1(X1))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_36])])).
% 0.99/1.17  cnf(c_0_65, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_35]), c_0_36])])).
% 0.99/1.17  fof(c_0_66, plain, ![X39]:(~v1_relat_1(X39)|k7_relat_1(X39,k1_relat_1(X39))=X39), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.99/1.17  cnf(c_0_67, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_31]), c_0_32])).
% 0.99/1.17  cnf(c_0_68, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.99/1.17  cnf(c_0_69, plain, (v1_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)))|~v1_relat_1(k1_relat_1(X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_62, c_0_44])).
% 0.99/1.17  cnf(c_0_70, plain, (k1_relat_1(k5_relat_1(k6_relat_1(k2_zfmisc_1(X1,X2)),k6_relat_1(k6_relat_1(X1))))=k8_relat_1(X2,k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_41]), c_0_36])])).
% 0.99/1.17  fof(c_0_71, plain, ![X19, X20]:(~v1_relat_1(X20)|k8_relat_1(X19,X20)=k5_relat_1(X20,k6_relat_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.99/1.17  cnf(c_0_72, plain, (k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X1)),X2))=k1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_40, c_0_47])).
% 0.99/1.17  cnf(c_0_73, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_58]), c_0_58]), c_0_36])])).
% 0.99/1.17  cnf(c_0_74, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.99/1.17  cnf(c_0_75, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_67, c_0_40])).
% 0.99/1.17  cnf(c_0_76, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k6_relat_1(X1),X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_43]), c_0_36])])).
% 0.99/1.17  cnf(c_0_77, plain, (v1_relat_1(k8_relat_1(X1,k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_41]), c_0_36]), c_0_36])])).
% 0.99/1.17  cnf(c_0_78, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.99/1.17  cnf(c_0_79, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(X2))))=k1_relat_1(k7_relat_1(X2,X1))|~v1_relat_1(X2)), inference(rw,[status(thm)],[c_0_72, c_0_56])).
% 0.99/1.17  cnf(c_0_80, plain, (r1_tarski(k8_relat_1(X1,X2),X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_67, c_0_46])).
% 0.99/1.17  cnf(c_0_81, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),X3))=k5_relat_1(k6_relat_1(X2),X3)|~v1_relat_1(X3)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_73]), c_0_36]), c_0_36])])).
% 0.99/1.17  cnf(c_0_82, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_74])).
% 0.99/1.17  cnf(c_0_83, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_41]), c_0_36])])).
% 0.99/1.17  cnf(c_0_84, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k5_relat_1(k6_relat_1(X1),X2),X3))=k5_relat_1(k5_relat_1(k6_relat_1(X1),X2),X3)|~v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_76]), c_0_36])])).
% 0.99/1.17  cnf(c_0_85, plain, (k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X2))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_44]), c_0_36])])).
% 0.99/1.17  cnf(c_0_86, plain, (v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_36])])).
% 0.99/1.17  cnf(c_0_87, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_65]), c_0_41])).
% 0.99/1.17  cnf(c_0_88, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_80, c_0_78])).
% 0.99/1.17  cnf(c_0_89, plain, (k5_relat_1(k6_relat_1(X1),X2)=X2|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.99/1.17  cnf(c_0_90, plain, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_44]), c_0_36])])).
% 0.99/1.17  cnf(c_0_91, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_relat_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_73]), c_0_41])).
% 0.99/1.17  cnf(c_0_92, plain, (k7_relat_1(k5_relat_1(X1,k5_relat_1(X2,X3)),X4)=k5_relat_1(k7_relat_1(k5_relat_1(X1,X2),X4),X3)|~v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_68])).
% 0.99/1.17  cnf(c_0_93, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_36])])).
% 0.99/1.17  cnf(c_0_94, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=X1|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_41]), c_0_56]), c_0_36])])).
% 0.99/1.17  cnf(c_0_95, plain, (r1_tarski(k5_relat_1(X1,k5_relat_1(X2,k6_relat_1(X3))),k5_relat_1(X1,X2))|~v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_68]), c_0_36])])).
% 0.99/1.17  cnf(c_0_96, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_86])])).
% 0.99/1.17  fof(c_0_97, plain, ![X23, X24]:(~v1_relat_1(X23)|(~v1_relat_1(X24)|r1_tarski(k2_relat_1(k5_relat_1(X23,X24)),k2_relat_1(X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).
% 0.99/1.17  cnf(c_0_98, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=X2|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_41]), c_0_56]), c_0_36])])).
% 0.99/1.17  cnf(c_0_99, plain, (k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3)=k5_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X1)),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_43]), c_0_56]), c_0_43]), c_0_36]), c_0_36]), c_0_36])])).
% 0.99/1.17  cnf(c_0_100, plain, (X1=X2|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_73]), c_0_41])).
% 0.99/1.17  cnf(c_0_101, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_86]), c_0_36]), c_0_36])])).
% 0.99/1.17  cnf(c_0_102, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.99/1.17  fof(c_0_103, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.99/1.17  cnf(c_0_104, plain, (k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_65]), c_0_36]), c_0_36])]), c_0_56]), c_0_56])).
% 0.99/1.17  cnf(c_0_105, plain, (k1_relat_1(k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3))=X2|~r1_tarski(X2,X3)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_98]), c_0_86])])).
% 0.99/1.17  cnf(c_0_106, plain, (k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X3))=k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_99]), c_0_86])])).
% 0.99/1.17  cnf(c_0_107, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_101])])).
% 0.99/1.17  cnf(c_0_108, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,k5_relat_1(X2,X3))),k2_relat_1(X3))|~v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_102, c_0_68])).
% 0.99/1.17  fof(c_0_109, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_103])])])).
% 0.99/1.17  cnf(c_0_110, plain, (k5_relat_1(k7_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2))),X2)=k5_relat_1(X1,X2)|~v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_74, c_0_42])).
% 0.99/1.17  cnf(c_0_111, plain, (k5_relat_1(k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3),k6_relat_1(X2))=k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_85]), c_0_36])]), c_0_86])])).
% 0.99/1.17  cnf(c_0_112, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_104, c_0_65])).
% 0.99/1.17  cnf(c_0_113, plain, (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X1,X2))),k2_relat_1(k4_relat_1(X1)))|~v1_relat_1(k4_relat_1(X1))|~v1_relat_1(k4_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_102, c_0_57])).
% 0.99/1.17  cnf(c_0_114, plain, (k4_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k5_relat_1(k6_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_36])])).
% 0.99/1.17  cnf(c_0_115, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))))=X3|~r1_tarski(X3,X1)|~r1_tarski(X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_99]), c_0_106])).
% 0.99/1.17  cnf(c_0_116, plain, (k5_relat_1(X1,k5_relat_1(X2,k6_relat_1(k2_relat_1(k5_relat_1(X1,X2)))))=k5_relat_1(X1,X2)|~v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_68]), c_0_36])])).
% 0.99/1.17  cnf(c_0_117, plain, (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_107]), c_0_35]), c_0_36]), c_0_36])])).
% 0.99/1.17  cnf(c_0_118, plain, (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_93]), c_0_35]), c_0_43]), c_0_36]), c_0_36]), c_0_36])])).
% 0.99/1.17  cnf(c_0_119, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.99/1.17  cnf(c_0_120, plain, (k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_85]), c_0_36])]), c_0_111]), c_0_86])])).
% 0.99/1.17  cnf(c_0_121, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X1)|~r1_tarski(X1,k1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))))), inference(spm,[status(thm)],[c_0_112, c_0_90])).
% 0.99/1.17  cnf(c_0_122, plain, (r1_tarski(k2_relat_1(k4_relat_1(X1)),k1_relat_1(X1))|~v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_82]), c_0_58]), c_0_35]), c_0_58]), c_0_36]), c_0_36])])).
% 0.99/1.17  cnf(c_0_123, plain, (k4_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_107]), c_0_58]), c_0_36])])).
% 0.99/1.17  cnf(c_0_124, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117]), c_0_118]), c_0_86]), c_0_36]), c_0_36])])).
% 0.99/1.17  cnf(c_0_125, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_31]), c_0_32])).
% 0.99/1.17  cnf(c_0_126, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_99]), c_0_107]), c_0_106]), c_0_107])).
% 0.99/1.17  cnf(c_0_127, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))))=k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_123]), c_0_124]), c_0_107]), c_0_123]), c_0_124]), c_0_123]), c_0_86]), c_0_86])])).
% 0.99/1.17  cnf(c_0_128, plain, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)),k1_relat_1(X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_75, c_0_44])).
% 0.99/1.17  cnf(c_0_129, negated_conjecture, (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk1_0),esk2_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_125, c_0_47])).
% 0.99/1.17  cnf(c_0_130, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_126, c_0_127])).
% 0.99/1.17  cnf(c_0_131, plain, (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_107]), c_0_41]), c_0_36])])).
% 0.99/1.17  cnf(c_0_132, negated_conjecture, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_44]), c_0_36])])).
% 0.99/1.17  cnf(c_0_133, plain, (k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_130]), c_0_131])])).
% 0.99/1.17  cnf(c_0_134, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132, c_0_133])]), ['proof']).
% 0.99/1.17  # SZS output end CNFRefutation
% 0.99/1.17  # Proof object total steps             : 135
% 0.99/1.17  # Proof object clause steps            : 94
% 0.99/1.17  # Proof object formula steps           : 41
% 0.99/1.17  # Proof object conjectures             : 8
% 0.99/1.17  # Proof object clause conjectures      : 5
% 0.99/1.17  # Proof object formula conjectures     : 3
% 0.99/1.17  # Proof object initial clauses used    : 21
% 0.99/1.17  # Proof object initial formulas used   : 20
% 0.99/1.17  # Proof object generating inferences   : 58
% 0.99/1.17  # Proof object simplifying inferences  : 157
% 0.99/1.17  # Training examples: 0 positive, 0 negative
% 0.99/1.17  # Parsed axioms                        : 20
% 0.99/1.17  # Removed by relevancy pruning/SinE    : 0
% 0.99/1.17  # Initial clauses                      : 21
% 0.99/1.17  # Removed in clause preprocessing      : 3
% 0.99/1.17  # Initial clauses in saturation        : 18
% 0.99/1.17  # Processed clauses                    : 4132
% 0.99/1.17  # ...of these trivial                  : 190
% 0.99/1.17  # ...subsumed                          : 3178
% 0.99/1.17  # ...remaining for further processing  : 764
% 0.99/1.17  # Other redundant clauses eliminated   : 0
% 0.99/1.17  # Clauses deleted for lack of memory   : 0
% 0.99/1.17  # Backward-subsumed                    : 14
% 0.99/1.17  # Backward-rewritten                   : 117
% 0.99/1.17  # Generated clauses                    : 77125
% 0.99/1.17  # ...of the previous two non-trivial   : 59535
% 0.99/1.17  # Contextual simplify-reflections      : 39
% 0.99/1.17  # Paramodulations                      : 77125
% 0.99/1.17  # Factorizations                       : 0
% 0.99/1.17  # Equation resolutions                 : 0
% 0.99/1.17  # Propositional unsat checks           : 0
% 0.99/1.17  #    Propositional check models        : 0
% 0.99/1.17  #    Propositional check unsatisfiable : 0
% 0.99/1.17  #    Propositional clauses             : 0
% 0.99/1.17  #    Propositional clauses after purity: 0
% 0.99/1.17  #    Propositional unsat core size     : 0
% 0.99/1.17  #    Propositional preprocessing time  : 0.000
% 0.99/1.17  #    Propositional encoding time       : 0.000
% 0.99/1.17  #    Propositional solver time         : 0.000
% 0.99/1.17  #    Success case prop preproc time    : 0.000
% 0.99/1.17  #    Success case prop encoding time   : 0.000
% 0.99/1.17  #    Success case prop solver time     : 0.000
% 0.99/1.17  # Current number of processed clauses  : 615
% 0.99/1.17  #    Positive orientable unit clauses  : 80
% 0.99/1.17  #    Positive unorientable unit clauses: 1
% 0.99/1.17  #    Negative unit clauses             : 2
% 0.99/1.17  #    Non-unit-clauses                  : 532
% 0.99/1.17  # Current number of unprocessed clauses: 55291
% 0.99/1.17  # ...number of literals in the above   : 211000
% 0.99/1.17  # Current number of archived formulas  : 0
% 0.99/1.17  # Current number of archived clauses   : 152
% 0.99/1.17  # Clause-clause subsumption calls (NU) : 59571
% 0.99/1.17  # Rec. Clause-clause subsumption calls : 43412
% 0.99/1.17  # Non-unit clause-clause subsumptions  : 3158
% 0.99/1.17  # Unit Clause-clause subsumption calls : 371
% 0.99/1.17  # Rewrite failures with RHS unbound    : 0
% 0.99/1.17  # BW rewrite match attempts            : 707
% 0.99/1.17  # BW rewrite match successes           : 116
% 0.99/1.17  # Condensation attempts                : 0
% 0.99/1.17  # Condensation successes               : 0
% 0.99/1.17  # Termbank termtop insertions          : 1807243
% 0.99/1.17  
% 0.99/1.17  # -------------------------------------------------
% 0.99/1.17  # User time                : 0.802 s
% 0.99/1.17  # System time              : 0.035 s
% 0.99/1.17  # Total time               : 0.837 s
% 0.99/1.17  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
