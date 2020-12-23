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
% DateTime   : Thu Dec  3 10:53:26 EST 2020

% Result     : Theorem 0.55s
% Output     : CNFRefutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  124 (6414 expanded)
%              Number of clauses        :   77 (2637 expanded)
%              Number of leaves         :   23 (1888 expanded)
%              Depth                    :   19
%              Number of atoms          :  201 (9714 expanded)
%              Number of equality atoms :   97 (5155 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t139_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k8_relat_1(X1,k5_relat_1(X2,X3)) = k5_relat_1(X2,k8_relat_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t43_funct_1,conjecture,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(c_0_23,plain,(
    ! [X66] :
      ( ~ v1_relat_1(X66)
      | k5_relat_1(X66,k6_relat_1(k2_relat_1(X66))) = X66 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_24,plain,(
    ! [X61] :
      ( k1_relat_1(k6_relat_1(X61)) = X61
      & k2_relat_1(k6_relat_1(X61)) = X61 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_25,plain,(
    ! [X45] : v1_relat_1(k6_relat_1(X45)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_26,plain,(
    ! [X51,X52,X53] :
      ( ~ v1_relat_1(X52)
      | ~ v1_relat_1(X53)
      | k8_relat_1(X51,k5_relat_1(X52,X53)) = k5_relat_1(X52,k8_relat_1(X51,X53)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_relat_1])])])).

cnf(c_0_27,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X49,X50] :
      ( ~ v1_relat_1(X50)
      | k8_relat_1(X49,X50) = k5_relat_1(X50,k6_relat_1(X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_31,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X43)
      | ~ v1_relat_1(X44)
      | v1_relat_1(k5_relat_1(X43,X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_32,plain,
    ( k8_relat_1(X3,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_34,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,k6_relat_1(X1))) = k8_relat_1(X2,k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_29])])).

cnf(c_0_37,plain,
    ( k5_relat_1(X1,k8_relat_1(X2,X3)) = k5_relat_1(k5_relat_1(X1,X3),k6_relat_1(X2))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_35])).

fof(c_0_38,plain,(
    ! [X41,X42] : k1_setfam_1(k2_tarski(X41,X42)) = k3_xboole_0(X41,X42) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_39,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_40,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_33]),c_0_29])])).

fof(c_0_41,plain,(
    ! [X69,X70] :
      ( ~ v1_relat_1(X70)
      | k7_relat_1(X70,X69) = k5_relat_1(k6_relat_1(X69),X70) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_42,plain,(
    ! [X46,X47,X48] :
      ( ~ v1_relat_1(X47)
      | ~ v1_relat_1(X48)
      | k7_relat_1(k5_relat_1(X47,X48),X46) = k5_relat_1(k7_relat_1(X47,X46),X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

fof(c_0_43,plain,(
    ! [X67,X68] :
      ( ~ v1_relat_1(X68)
      | k1_relat_1(k7_relat_1(X68,X67)) = k3_xboole_0(k1_relat_1(X68),X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_44,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_46,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_47,plain,(
    ! [X19,X20,X21,X22] : k3_enumset1(X19,X19,X20,X21,X22) = k2_enumset1(X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_48,plain,(
    ! [X23,X24,X25,X26,X27] : k4_enumset1(X23,X23,X24,X25,X26,X27) = k3_enumset1(X23,X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_49,plain,(
    ! [X28,X29,X30,X31,X32,X33] : k5_enumset1(X28,X28,X29,X30,X31,X32,X33) = k4_enumset1(X28,X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_50,plain,(
    ! [X34,X35,X36,X37,X38,X39,X40] : k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40) = k5_enumset1(X34,X35,X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_51,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_52,plain,
    ( k5_relat_1(k5_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X3)) = k5_relat_1(X1,k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_40]),c_0_29])])).

cnf(c_0_53,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) = k5_relat_1(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_29]),c_0_29])])).

cnf(c_0_64,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_33]),c_0_29])])).

cnf(c_0_65,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_61])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_61])).

fof(c_0_67,plain,(
    ! [X64,X65] :
      ( ~ v1_relat_1(X65)
      | ~ r1_tarski(k1_relat_1(X65),X64)
      | k5_relat_1(k6_relat_1(X64),X65) = X65 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

cnf(c_0_68,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_27]),c_0_28]),c_0_64]),c_0_29])])).

cnf(c_0_69,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_53]),c_0_29])])).

fof(c_0_70,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2)) = k1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_73,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_74,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k2_tarski(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_75,plain,
    ( k8_relat_1(X1,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_68])).

cnf(c_0_76,plain,
    ( v1_relat_1(k5_relat_1(k7_relat_1(X1,X2),X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_54]),c_0_35])).

cnf(c_0_77,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_78,negated_conjecture,(
    ~ ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t43_funct_1])).

cnf(c_0_79,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_29])])).

cnf(c_0_80,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_72]),c_0_29])])).

cnf(c_0_81,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_82,plain,
    ( k5_relat_1(X1,k7_relat_1(k6_relat_1(X2),k2_relat_1(X1))) = k8_relat_1(X2,X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_29])]),c_0_75])).

cnf(c_0_83,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_64]),c_0_29])])).

cnf(c_0_84,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_61])).

fof(c_0_85,negated_conjecture,(
    k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_78])])])).

cnf(c_0_86,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X1)),X2)) = k1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_71,c_0_79])).

cnf(c_0_87,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_80]),c_0_29])])).

cnf(c_0_88,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_79])).

cnf(c_0_89,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_45]),c_0_45]),c_0_57]),c_0_57]),c_0_58]),c_0_58]),c_0_59]),c_0_59]),c_0_60]),c_0_60]),c_0_61]),c_0_61])).

fof(c_0_90,plain,(
    ! [X62,X63] :
      ( ( r1_tarski(k5_relat_1(X63,k6_relat_1(X62)),X63)
        | ~ v1_relat_1(X63) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X62),X63),X63)
        | ~ v1_relat_1(X63) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

cnf(c_0_91,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_82]),c_0_83])])).

cnf(c_0_92,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_84,c_0_66])).

cnf(c_0_93,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

fof(c_0_94,plain,(
    ! [X56,X57] :
      ( ~ v1_relat_1(X56)
      | ~ v1_relat_1(X57)
      | r1_tarski(k2_relat_1(k5_relat_1(X56,X57)),k2_relat_1(X57)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

cnf(c_0_95,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_72])).

cnf(c_0_96,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_66]),c_0_79])).

cnf(c_0_97,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_98,plain,
    ( k5_relat_1(k5_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X3)) = k5_relat_1(X1,k7_relat_1(k6_relat_1(X3),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_52,c_0_68])).

cnf(c_0_99,plain,
    ( v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_34])).

cnf(c_0_100,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_71])).

cnf(c_0_101,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) != k6_relat_1(k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_61])).

cnf(c_0_102,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_103,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_72]),c_0_29]),c_0_72])])).

cnf(c_0_104,plain,
    ( r1_tarski(k5_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3)),k5_relat_1(X1,k6_relat_1(X3)))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])).

cnf(c_0_105,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),k7_relat_1(X1,X2)) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_100]),c_0_69])).

cnf(c_0_106,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_101,c_0_89])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_33]),c_0_28]),c_0_28]),c_0_29])])).

cnf(c_0_108,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_103]),c_0_72]),c_0_29]),c_0_72])])).

cnf(c_0_109,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_72]),c_0_68]),c_0_72]),c_0_29]),c_0_29])])).

cnf(c_0_110,negated_conjecture,
    ( k6_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_106,c_0_66])).

cnf(c_0_111,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_107])).

cnf(c_0_112,plain,
    ( k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,X3)) = k8_relat_1(X2,k7_relat_1(X3,X1))
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_53]),c_0_29])])).

cnf(c_0_113,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_109])])).

cnf(c_0_114,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0))) != k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_110,c_0_79])).

cnf(c_0_115,plain,
    ( k8_relat_1(X1,k7_relat_1(X2,k1_relat_1(k8_relat_1(X1,X2)))) = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_91])).

cnf(c_0_116,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_113])).

cnf(c_0_117,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_96]),c_0_72]),c_0_29])])).

cnf(c_0_118,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0))) != k7_relat_1(k6_relat_1(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_114,c_0_68])).

cnf(c_0_119,plain,
    ( k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_40]),c_0_68]),c_0_75]),c_0_40]),c_0_68]),c_0_29]),c_0_40]),c_0_68]),c_0_117])])).

cnf(c_0_120,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_72]),c_0_29])])).

cnf(c_0_121,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0))) != k7_relat_1(k6_relat_1(esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_118,c_0_113])).

cnf(c_0_122,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_119]),c_0_120])])).

cnf(c_0_123,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_122])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:11:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.55/0.74  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.55/0.74  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.55/0.74  #
% 0.55/0.74  # Preprocessing time       : 0.028 s
% 0.55/0.74  # Presaturation interreduction done
% 0.55/0.74  
% 0.55/0.74  # Proof found!
% 0.55/0.74  # SZS status Theorem
% 0.55/0.74  # SZS output start CNFRefutation
% 0.55/0.74  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 0.55/0.74  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.55/0.74  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.55/0.74  fof(t139_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k8_relat_1(X1,k5_relat_1(X2,X3))=k5_relat_1(X2,k8_relat_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 0.55/0.74  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 0.55/0.74  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.55/0.74  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.55/0.74  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.55/0.74  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.55/0.74  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 0.55/0.74  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.55/0.74  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.55/0.74  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.55/0.74  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.55/0.74  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.55/0.74  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.55/0.74  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.55/0.74  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 0.55/0.74  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.55/0.74  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.55/0.74  fof(t43_funct_1, conjecture, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.55/0.74  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 0.55/0.74  fof(t45_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 0.55/0.74  fof(c_0_23, plain, ![X66]:(~v1_relat_1(X66)|k5_relat_1(X66,k6_relat_1(k2_relat_1(X66)))=X66), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.55/0.74  fof(c_0_24, plain, ![X61]:(k1_relat_1(k6_relat_1(X61))=X61&k2_relat_1(k6_relat_1(X61))=X61), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.55/0.74  fof(c_0_25, plain, ![X45]:v1_relat_1(k6_relat_1(X45)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.55/0.74  fof(c_0_26, plain, ![X51, X52, X53]:(~v1_relat_1(X52)|(~v1_relat_1(X53)|k8_relat_1(X51,k5_relat_1(X52,X53))=k5_relat_1(X52,k8_relat_1(X51,X53)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_relat_1])])])).
% 0.55/0.74  cnf(c_0_27, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.55/0.74  cnf(c_0_28, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.55/0.74  cnf(c_0_29, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.55/0.74  fof(c_0_30, plain, ![X49, X50]:(~v1_relat_1(X50)|k8_relat_1(X49,X50)=k5_relat_1(X50,k6_relat_1(X49))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.55/0.74  fof(c_0_31, plain, ![X43, X44]:(~v1_relat_1(X43)|~v1_relat_1(X44)|v1_relat_1(k5_relat_1(X43,X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.55/0.74  cnf(c_0_32, plain, (k8_relat_1(X3,k5_relat_1(X1,X2))=k5_relat_1(X1,k8_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.55/0.74  cnf(c_0_33, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.55/0.74  cnf(c_0_34, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.55/0.74  cnf(c_0_35, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.55/0.74  cnf(c_0_36, plain, (k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,k6_relat_1(X1)))=k8_relat_1(X2,k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_29])])).
% 0.55/0.74  cnf(c_0_37, plain, (k5_relat_1(X1,k8_relat_1(X2,X3))=k5_relat_1(k5_relat_1(X1,X3),k6_relat_1(X2))|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_32]), c_0_35])).
% 0.55/0.74  fof(c_0_38, plain, ![X41, X42]:k1_setfam_1(k2_tarski(X41,X42))=k3_xboole_0(X41,X42), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.55/0.74  fof(c_0_39, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.55/0.74  cnf(c_0_40, plain, (k8_relat_1(X1,k6_relat_1(X2))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_33]), c_0_29])])).
% 0.55/0.74  fof(c_0_41, plain, ![X69, X70]:(~v1_relat_1(X70)|k7_relat_1(X70,X69)=k5_relat_1(k6_relat_1(X69),X70)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.55/0.74  fof(c_0_42, plain, ![X46, X47, X48]:(~v1_relat_1(X47)|(~v1_relat_1(X48)|k7_relat_1(k5_relat_1(X47,X48),X46)=k5_relat_1(k7_relat_1(X47,X46),X48))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 0.55/0.74  fof(c_0_43, plain, ![X67, X68]:(~v1_relat_1(X68)|k1_relat_1(k7_relat_1(X68,X67))=k3_xboole_0(k1_relat_1(X68),X67)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.55/0.74  cnf(c_0_44, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.55/0.74  cnf(c_0_45, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.55/0.74  fof(c_0_46, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.55/0.74  fof(c_0_47, plain, ![X19, X20, X21, X22]:k3_enumset1(X19,X19,X20,X21,X22)=k2_enumset1(X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.55/0.74  fof(c_0_48, plain, ![X23, X24, X25, X26, X27]:k4_enumset1(X23,X23,X24,X25,X26,X27)=k3_enumset1(X23,X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.55/0.74  fof(c_0_49, plain, ![X28, X29, X30, X31, X32, X33]:k5_enumset1(X28,X28,X29,X30,X31,X32,X33)=k4_enumset1(X28,X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.55/0.74  fof(c_0_50, plain, ![X34, X35, X36, X37, X38, X39, X40]:k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40)=k5_enumset1(X34,X35,X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.55/0.74  fof(c_0_51, plain, ![X10, X11]:k4_xboole_0(X10,k4_xboole_0(X10,X11))=k3_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.55/0.74  cnf(c_0_52, plain, (k5_relat_1(k5_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X3))=k5_relat_1(X1,k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_40]), c_0_29])])).
% 0.55/0.74  cnf(c_0_53, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.55/0.74  cnf(c_0_54, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.55/0.74  cnf(c_0_55, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.55/0.74  cnf(c_0_56, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.55/0.74  cnf(c_0_57, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.55/0.74  cnf(c_0_58, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.55/0.74  cnf(c_0_59, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.55/0.74  cnf(c_0_60, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.55/0.74  cnf(c_0_61, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.55/0.74  cnf(c_0_62, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.55/0.74  cnf(c_0_63, plain, (k5_relat_1(k6_relat_1(X1),k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))=k5_relat_1(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_29]), c_0_29])])).
% 0.55/0.74  cnf(c_0_64, plain, (k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_33]), c_0_29])])).
% 0.55/0.74  cnf(c_0_65, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60]), c_0_61])).
% 0.55/0.74  cnf(c_0_66, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60]), c_0_61])).
% 0.55/0.74  fof(c_0_67, plain, ![X64, X65]:(~v1_relat_1(X65)|(~r1_tarski(k1_relat_1(X65),X64)|k5_relat_1(k6_relat_1(X64),X65)=X65)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.55/0.74  cnf(c_0_68, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_27]), c_0_28]), c_0_64]), c_0_29])])).
% 0.55/0.74  cnf(c_0_69, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_53]), c_0_29])])).
% 0.55/0.74  fof(c_0_70, plain, ![X8, X9]:r1_tarski(k3_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.55/0.74  cnf(c_0_71, plain, (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2))=k1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 0.55/0.74  cnf(c_0_72, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.55/0.74  cnf(c_0_73, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.55/0.74  fof(c_0_74, plain, ![X12, X13]:k2_tarski(X12,X13)=k2_tarski(X13,X12), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.55/0.74  cnf(c_0_75, plain, (k8_relat_1(X1,k6_relat_1(X2))=k7_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[c_0_40, c_0_68])).
% 0.55/0.74  cnf(c_0_76, plain, (v1_relat_1(k5_relat_1(k7_relat_1(X1,X2),X3))|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_54]), c_0_35])).
% 0.55/0.74  cnf(c_0_77, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.55/0.74  fof(c_0_78, negated_conjecture, ~(![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t43_funct_1])).
% 0.55/0.74  cnf(c_0_79, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_29])])).
% 0.55/0.74  cnf(c_0_80, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_72]), c_0_29])])).
% 0.55/0.74  cnf(c_0_81, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.55/0.74  cnf(c_0_82, plain, (k5_relat_1(X1,k7_relat_1(k6_relat_1(X2),k2_relat_1(X1)))=k8_relat_1(X2,X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_27]), c_0_29])]), c_0_75])).
% 0.55/0.74  cnf(c_0_83, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_64]), c_0_29])])).
% 0.55/0.74  cnf(c_0_84, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60]), c_0_61])).
% 0.55/0.74  fof(c_0_85, negated_conjecture, k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_78])])])).
% 0.55/0.74  cnf(c_0_86, plain, (k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X1)),X2))=k1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_71, c_0_79])).
% 0.55/0.74  cnf(c_0_87, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_80]), c_0_29])])).
% 0.55/0.74  cnf(c_0_88, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(rw,[status(thm)],[c_0_66, c_0_79])).
% 0.55/0.74  cnf(c_0_89, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_45]), c_0_45]), c_0_57]), c_0_57]), c_0_58]), c_0_58]), c_0_59]), c_0_59]), c_0_60]), c_0_60]), c_0_61]), c_0_61])).
% 0.55/0.74  fof(c_0_90, plain, ![X62, X63]:((r1_tarski(k5_relat_1(X63,k6_relat_1(X62)),X63)|~v1_relat_1(X63))&(r1_tarski(k5_relat_1(k6_relat_1(X62),X63),X63)|~v1_relat_1(X63))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.55/0.74  cnf(c_0_91, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_82]), c_0_83])])).
% 0.55/0.74  cnf(c_0_92, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_84, c_0_66])).
% 0.55/0.74  cnf(c_0_93, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.55/0.74  fof(c_0_94, plain, ![X56, X57]:(~v1_relat_1(X56)|(~v1_relat_1(X57)|r1_tarski(k2_relat_1(k5_relat_1(X56,X57)),k2_relat_1(X57)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).
% 0.55/0.74  cnf(c_0_95, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_relat_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_72])).
% 0.55/0.74  cnf(c_0_96, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_66]), c_0_79])).
% 0.55/0.74  cnf(c_0_97, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.55/0.74  cnf(c_0_98, plain, (k5_relat_1(k5_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X3))=k5_relat_1(X1,k7_relat_1(k6_relat_1(X3),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_52, c_0_68])).
% 0.55/0.74  cnf(c_0_99, plain, (v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_91, c_0_34])).
% 0.55/0.74  cnf(c_0_100, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_92, c_0_71])).
% 0.55/0.74  cnf(c_0_101, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))!=k6_relat_1(k1_setfam_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60]), c_0_61])).
% 0.55/0.74  cnf(c_0_102, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.55/0.74  cnf(c_0_103, plain, (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))=X2|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_72]), c_0_29]), c_0_72])])).
% 0.55/0.74  cnf(c_0_104, plain, (r1_tarski(k5_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3)),k5_relat_1(X1,k6_relat_1(X3)))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])).
% 0.55/0.74  cnf(c_0_105, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),k7_relat_1(X1,X2))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_100]), c_0_69])).
% 0.55/0.74  cnf(c_0_106, negated_conjecture, (k6_relat_1(k1_setfam_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk1_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_101, c_0_89])).
% 0.55/0.74  cnf(c_0_107, plain, (r1_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_33]), c_0_28]), c_0_28]), c_0_29])])).
% 0.55/0.74  cnf(c_0_108, plain, (X1=X2|~r1_tarski(X2,X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_103]), c_0_72]), c_0_29]), c_0_72])])).
% 0.55/0.74  cnf(c_0_109, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k7_relat_1(k6_relat_1(X2),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_72]), c_0_68]), c_0_72]), c_0_29]), c_0_29])])).
% 0.55/0.74  cnf(c_0_110, negated_conjecture, (k6_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_106, c_0_66])).
% 0.55/0.74  cnf(c_0_111, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_73, c_0_107])).
% 0.55/0.74  cnf(c_0_112, plain, (k5_relat_1(k6_relat_1(X1),k8_relat_1(X2,X3))=k8_relat_1(X2,k7_relat_1(X3,X1))|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_53]), c_0_29])])).
% 0.55/0.74  cnf(c_0_113, plain, (k7_relat_1(k6_relat_1(X1),X2)=k7_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_109])])).
% 0.55/0.74  cnf(c_0_114, negated_conjecture, (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0)))!=k5_relat_1(k6_relat_1(esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_110, c_0_79])).
% 0.55/0.74  cnf(c_0_115, plain, (k8_relat_1(X1,k7_relat_1(X2,k1_relat_1(k8_relat_1(X1,X2))))=k8_relat_1(X1,X2)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_91])).
% 0.55/0.74  cnf(c_0_116, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_87, c_0_113])).
% 0.55/0.74  cnf(c_0_117, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_96]), c_0_72]), c_0_29])])).
% 0.55/0.74  cnf(c_0_118, negated_conjecture, (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0)))!=k7_relat_1(k6_relat_1(esk1_0),esk2_0)), inference(rw,[status(thm)],[c_0_114, c_0_68])).
% 0.55/0.74  cnf(c_0_119, plain, (k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_40]), c_0_68]), c_0_75]), c_0_40]), c_0_68]), c_0_29]), c_0_40]), c_0_68]), c_0_117])])).
% 0.55/0.74  cnf(c_0_120, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_72]), c_0_29])])).
% 0.55/0.74  cnf(c_0_121, negated_conjecture, (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(esk2_0),esk1_0)))!=k7_relat_1(k6_relat_1(esk2_0),esk1_0)), inference(rw,[status(thm)],[c_0_118, c_0_113])).
% 0.55/0.74  cnf(c_0_122, plain, (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))=k7_relat_1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_119]), c_0_120])])).
% 0.55/0.74  cnf(c_0_123, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_122])]), ['proof']).
% 0.55/0.74  # SZS output end CNFRefutation
% 0.55/0.74  # Proof object total steps             : 124
% 0.55/0.74  # Proof object clause steps            : 77
% 0.55/0.74  # Proof object formula steps           : 47
% 0.55/0.74  # Proof object conjectures             : 11
% 0.55/0.74  # Proof object clause conjectures      : 8
% 0.55/0.74  # Proof object formula conjectures     : 3
% 0.55/0.74  # Proof object initial clauses used    : 24
% 0.55/0.74  # Proof object initial formulas used   : 23
% 0.55/0.74  # Proof object generating inferences   : 35
% 0.55/0.74  # Proof object simplifying inferences  : 130
% 0.55/0.74  # Training examples: 0 positive, 0 negative
% 0.55/0.74  # Parsed axioms                        : 25
% 0.55/0.74  # Removed by relevancy pruning/SinE    : 0
% 0.55/0.74  # Initial clauses                      : 27
% 0.55/0.74  # Removed in clause preprocessing      : 7
% 0.55/0.74  # Initial clauses in saturation        : 20
% 0.55/0.74  # Processed clauses                    : 2520
% 0.55/0.74  # ...of these trivial                  : 72
% 0.55/0.74  # ...subsumed                          : 1917
% 0.55/0.74  # ...remaining for further processing  : 531
% 0.55/0.74  # Other redundant clauses eliminated   : 0
% 0.55/0.74  # Clauses deleted for lack of memory   : 0
% 0.55/0.74  # Backward-subsumed                    : 7
% 0.55/0.74  # Backward-rewritten                   : 47
% 0.55/0.74  # Generated clauses                    : 30214
% 0.55/0.74  # ...of the previous two non-trivial   : 25800
% 0.55/0.74  # Contextual simplify-reflections      : 93
% 0.55/0.74  # Paramodulations                      : 30214
% 0.55/0.74  # Factorizations                       : 0
% 0.55/0.74  # Equation resolutions                 : 0
% 0.55/0.74  # Propositional unsat checks           : 0
% 0.55/0.74  #    Propositional check models        : 0
% 0.55/0.74  #    Propositional check unsatisfiable : 0
% 0.55/0.74  #    Propositional clauses             : 0
% 0.55/0.74  #    Propositional clauses after purity: 0
% 0.55/0.74  #    Propositional unsat core size     : 0
% 0.55/0.74  #    Propositional preprocessing time  : 0.000
% 0.55/0.74  #    Propositional encoding time       : 0.000
% 0.55/0.74  #    Propositional solver time         : 0.000
% 0.55/0.74  #    Success case prop preproc time    : 0.000
% 0.55/0.74  #    Success case prop encoding time   : 0.000
% 0.55/0.74  #    Success case prop solver time     : 0.000
% 0.55/0.74  # Current number of processed clauses  : 457
% 0.55/0.74  #    Positive orientable unit clauses  : 56
% 0.55/0.74  #    Positive unorientable unit clauses: 2
% 0.55/0.74  #    Negative unit clauses             : 2
% 0.55/0.74  #    Non-unit-clauses                  : 397
% 0.55/0.74  # Current number of unprocessed clauses: 23203
% 0.55/0.74  # ...number of literals in the above   : 74167
% 0.55/0.74  # Current number of archived formulas  : 0
% 0.55/0.74  # Current number of archived clauses   : 81
% 0.55/0.74  # Clause-clause subsumption calls (NU) : 19818
% 0.55/0.74  # Rec. Clause-clause subsumption calls : 18321
% 0.55/0.74  # Non-unit clause-clause subsumptions  : 1996
% 0.55/0.74  # Unit Clause-clause subsumption calls : 48
% 0.55/0.74  # Rewrite failures with RHS unbound    : 0
% 0.55/0.74  # BW rewrite match attempts            : 233
% 0.55/0.74  # BW rewrite match successes           : 93
% 0.55/0.74  # Condensation attempts                : 0
% 0.55/0.74  # Condensation successes               : 0
% 0.55/0.74  # Termbank termtop insertions          : 543086
% 0.55/0.74  
% 0.55/0.74  # -------------------------------------------------
% 0.55/0.74  # User time                : 0.394 s
% 0.55/0.74  # System time              : 0.018 s
% 0.55/0.74  # Total time               : 0.412 s
% 0.55/0.74  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
