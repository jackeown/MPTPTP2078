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
% DateTime   : Thu Dec  3 11:07:27 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 (4551 expanded)
%              Number of clauses        :   71 (2106 expanded)
%              Number of leaves         :   17 (1221 expanded)
%              Depth                    :   19
%              Number of atoms          :  179 (5594 expanded)
%              Number of equality atoms :   82 (4042 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t148_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t175_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(k10_relat_1(X1,X3),X2)
         => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(c_0_17,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X16,X17] : k1_setfam_1(k2_tarski(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_19,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_23,plain,(
    ! [X32,X33] : k5_relat_1(k6_relat_1(X33),k6_relat_1(X32)) = k6_relat_1(k3_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_24,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X10] : k4_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_28,plain,(
    ! [X20] :
      ( k1_relat_1(k6_relat_1(X20)) = X20
      & k2_relat_1(k6_relat_1(X20)) = X20 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_29,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X11] :
      ( ~ r1_tarski(X11,k1_xboole_0)
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_31,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_21]),c_0_25]),c_0_25])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X14,X15] : k2_tarski(X14,X15) = k2_tarski(X15,X14) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_35,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_21])).

fof(c_0_37,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | k7_relat_1(X22,X21) = k5_relat_1(k6_relat_1(X21),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_38,plain,(
    ! [X23] :
      ( v1_relat_1(k6_relat_1(X23))
      & v1_funct_1(k6_relat_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_42,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(k1_xboole_0,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

fof(c_0_49,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | k2_relat_1(k7_relat_1(X19,X18)) = k9_relat_1(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_50,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_42])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_42])).

fof(c_0_53,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | k9_relat_1(X28,k10_relat_1(X28,X27)) = k3_xboole_0(X27,k9_relat_1(X28,k1_relat_1(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).

fof(c_0_54,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | k10_relat_1(k7_relat_1(X26,X24),X25) = k3_xboole_0(X24,k10_relat_1(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_55,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_48])).

cnf(c_0_56,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_50]),c_0_51])).

fof(c_0_58,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | ~ r1_tarski(X29,k1_relat_1(X31))
      | ~ r1_tarski(k9_relat_1(X31,X29),X30)
      | r1_tarski(X29,k10_relat_1(X31,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_59,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_48])).

cnf(c_0_60,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_48])).

cnf(c_0_63,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k9_relat_1(k6_relat_1(X2),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_45])])).

cnf(c_0_64,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_57]),c_0_50]),c_0_51])).

fof(c_0_65,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_66,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_56]),c_0_45])])).

cnf(c_0_68,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_69,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_70,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k1_setfam_1(k2_tarski(X2,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_60,c_0_21])).

cnf(c_0_71,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k2_tarski(X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_61,c_0_21])).

cnf(c_0_72,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_35])).

cnf(c_0_73,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_64])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_75,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X2),X1))
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_45]),c_0_69])])).

cnf(c_0_77,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_70])).

cnf(c_0_78,plain,
    ( k9_relat_1(k6_relat_1(X1),k10_relat_1(X2,X3)) = k10_relat_1(k7_relat_1(X2,X1),X3)
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_48]),c_0_72])).

cnf(c_0_79,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_73]),c_0_45])])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_81,plain,
    ( k10_relat_1(k6_relat_1(X1),X2) = X2
    | ~ r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_68]),c_0_45])])).

cnf(c_0_83,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1) ),
    inference(rw,[status(thm)],[c_0_40,c_0_48])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_80])).

cnf(c_0_85,plain,
    ( k10_relat_1(k6_relat_1(X1),X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_86,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_56]),c_0_45])])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,k9_relat_1(k6_relat_1(X2),X1))
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_68]),c_0_45]),c_0_69]),c_0_86])])).

cnf(c_0_88,plain,
    ( k9_relat_1(k6_relat_1(X1),k9_relat_1(X2,k1_relat_1(X2))) = k9_relat_1(X2,k10_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_48]),c_0_72])).

cnf(c_0_89,plain,
    ( k9_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_79]),c_0_35]),c_0_45])])).

cnf(c_0_90,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_71])).

fof(c_0_91,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(k10_relat_1(X1,X3),X2)
           => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_2])).

cnf(c_0_92,plain,
    ( k9_relat_1(k6_relat_1(X1),X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_87]),c_0_67])])).

cnf(c_0_93,plain,
    ( k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_69]),c_0_89]),c_0_68]),c_0_45])])).

cnf(c_0_94,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_79]),c_0_45])])).

cnf(c_0_95,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[c_0_48,c_0_72])).

fof(c_0_96,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)
    & k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_91])])])).

cnf(c_0_97,plain,
    ( k9_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k6_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])])).

cnf(c_0_98,plain,
    ( k9_relat_1(k6_relat_1(X1),X2) = k9_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_42]),c_0_48]),c_0_72])).

cnf(c_0_99,negated_conjecture,
    ( k10_relat_1(esk1_0,esk3_0) != k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_100,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k10_relat_1(k6_relat_1(k10_relat_1(X1,X3)),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_78,c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_102,plain,
    ( k10_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k6_relat_1(X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_97]),c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( k10_relat_1(k6_relat_1(esk2_0),k10_relat_1(esk1_0,esk3_0)) != k10_relat_1(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101])]),c_0_102])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_85]),c_0_104])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.56  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.56  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.56  #
% 0.20/0.56  # Preprocessing time       : 0.046 s
% 0.20/0.56  # Presaturation interreduction done
% 0.20/0.56  
% 0.20/0.56  # Proof found!
% 0.20/0.56  # SZS status Theorem
% 0.20/0.56  # SZS output start CNFRefutation
% 0.20/0.56  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.56  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.56  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.56  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.56  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.20/0.56  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.56  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.56  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.20/0.56  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.56  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.20/0.56  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.20/0.56  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.20/0.56  fof(t148_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 0.20/0.56  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.20/0.56  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 0.20/0.56  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.56  fof(t175_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 0.20/0.56  fof(c_0_17, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.56  fof(c_0_18, plain, ![X16, X17]:k1_setfam_1(k2_tarski(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.56  fof(c_0_19, plain, ![X8, X9]:r1_tarski(k4_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.56  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.56  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.56  fof(c_0_22, plain, ![X12, X13]:k4_xboole_0(X12,k4_xboole_0(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.56  fof(c_0_23, plain, ![X32, X33]:k5_relat_1(k6_relat_1(X33),k6_relat_1(X32))=k6_relat_1(k3_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.20/0.56  cnf(c_0_24, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.56  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.56  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.56  fof(c_0_27, plain, ![X10]:k4_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.56  fof(c_0_28, plain, ![X20]:(k1_relat_1(k6_relat_1(X20))=X20&k2_relat_1(k6_relat_1(X20))=X20), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.56  cnf(c_0_29, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.56  fof(c_0_30, plain, ![X11]:(~r1_tarski(X11,k1_xboole_0)|X11=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.20/0.56  cnf(c_0_31, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))),X1)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.56  cnf(c_0_32, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_21]), c_0_25]), c_0_25])).
% 0.20/0.56  cnf(c_0_33, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.56  fof(c_0_34, plain, ![X14, X15]:k2_tarski(X14,X15)=k2_tarski(X15,X14), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.56  cnf(c_0_35, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.56  cnf(c_0_36, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k2_tarski(X2,X1)))), inference(rw,[status(thm)],[c_0_29, c_0_21])).
% 0.20/0.56  fof(c_0_37, plain, ![X21, X22]:(~v1_relat_1(X22)|k7_relat_1(X22,X21)=k5_relat_1(k6_relat_1(X21),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.20/0.56  fof(c_0_38, plain, ![X23]:(v1_relat_1(k6_relat_1(X23))&v1_funct_1(k6_relat_1(X23))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.20/0.56  cnf(c_0_39, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.56  cnf(c_0_40, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.56  cnf(c_0_41, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_33, c_0_25])).
% 0.20/0.56  cnf(c_0_42, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.56  cnf(c_0_43, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k1_setfam_1(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.56  cnf(c_0_44, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.56  cnf(c_0_45, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.56  cnf(c_0_46, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.56  cnf(c_0_47, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(k1_xboole_0,X1)))=X1), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.56  cnf(c_0_48, plain, (k1_setfam_1(k2_tarski(X1,X2))=k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.20/0.56  fof(c_0_49, plain, ![X18, X19]:(~v1_relat_1(X19)|k2_relat_1(k7_relat_1(X19,X18))=k9_relat_1(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.20/0.56  cnf(c_0_50, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_42])).
% 0.20/0.56  cnf(c_0_51, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_47, c_0_46])).
% 0.20/0.56  cnf(c_0_52, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_40, c_0_42])).
% 0.20/0.56  fof(c_0_53, plain, ![X27, X28]:(~v1_relat_1(X28)|~v1_funct_1(X28)|k9_relat_1(X28,k10_relat_1(X28,X27))=k3_xboole_0(X27,k9_relat_1(X28,k1_relat_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).
% 0.20/0.56  fof(c_0_54, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|k10_relat_1(k7_relat_1(X26,X24),X25)=k3_xboole_0(X24,k10_relat_1(X26,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.20/0.56  cnf(c_0_55, plain, (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)))=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(rw,[status(thm)],[c_0_36, c_0_48])).
% 0.20/0.56  cnf(c_0_56, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.56  cnf(c_0_57, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_50]), c_0_51])).
% 0.20/0.56  fof(c_0_58, plain, ![X29, X30, X31]:(~v1_relat_1(X31)|~v1_funct_1(X31)|(~r1_tarski(X29,k1_relat_1(X31))|~r1_tarski(k9_relat_1(X31,X29),X30)|r1_tarski(X29,k10_relat_1(X31,X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.20/0.56  cnf(c_0_59, plain, (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2)), inference(rw,[status(thm)],[c_0_52, c_0_48])).
% 0.20/0.56  cnf(c_0_60, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.56  cnf(c_0_61, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.56  cnf(c_0_62, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))), inference(rw,[status(thm)],[c_0_43, c_0_48])).
% 0.20/0.56  cnf(c_0_63, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k9_relat_1(k6_relat_1(X2),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_45])])).
% 0.20/0.56  cnf(c_0_64, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_57]), c_0_50]), c_0_51])).
% 0.20/0.56  fof(c_0_65, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.56  cnf(c_0_66, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.56  cnf(c_0_67, plain, (r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_56]), c_0_45])])).
% 0.20/0.56  cnf(c_0_68, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.56  cnf(c_0_69, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.56  cnf(c_0_70, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k1_setfam_1(k2_tarski(X2,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[c_0_60, c_0_21])).
% 0.20/0.56  cnf(c_0_71, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k2_tarski(X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_61, c_0_21])).
% 0.20/0.56  cnf(c_0_72, plain, (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k9_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_35])).
% 0.20/0.56  cnf(c_0_73, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_64])).
% 0.20/0.56  cnf(c_0_74, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.56  cnf(c_0_75, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.56  cnf(c_0_76, plain, (r1_tarski(X1,k10_relat_1(k6_relat_1(X2),X1))|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_45]), c_0_69])])).
% 0.20/0.56  cnf(c_0_77, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_70])).
% 0.20/0.56  cnf(c_0_78, plain, (k9_relat_1(k6_relat_1(X1),k10_relat_1(X2,X3))=k10_relat_1(k7_relat_1(X2,X1),X3)|~v1_relat_1(X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_48]), c_0_72])).
% 0.20/0.56  cnf(c_0_79, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_73]), c_0_45])])).
% 0.20/0.56  cnf(c_0_80, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_74])).
% 0.20/0.56  cnf(c_0_81, plain, (k10_relat_1(k6_relat_1(X1),X2)=X2|~r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.56  cnf(c_0_82, plain, (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79]), c_0_68]), c_0_45])])).
% 0.20/0.56  cnf(c_0_83, plain, (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)), inference(rw,[status(thm)],[c_0_40, c_0_48])).
% 0.20/0.56  cnf(c_0_84, plain, (r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_66, c_0_80])).
% 0.20/0.56  cnf(c_0_85, plain, (k10_relat_1(k6_relat_1(X1),X2)=X2|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 0.20/0.56  cnf(c_0_86, plain, (r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_56]), c_0_45])])).
% 0.20/0.56  cnf(c_0_87, plain, (r1_tarski(X1,k9_relat_1(k6_relat_1(X2),X1))|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_68]), c_0_45]), c_0_69]), c_0_86])])).
% 0.20/0.56  cnf(c_0_88, plain, (k9_relat_1(k6_relat_1(X1),k9_relat_1(X2,k1_relat_1(X2)))=k9_relat_1(X2,k10_relat_1(X2,X1))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_48]), c_0_72])).
% 0.20/0.56  cnf(c_0_89, plain, (k9_relat_1(k6_relat_1(X1),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_79]), c_0_35]), c_0_45])])).
% 0.20/0.56  cnf(c_0_90, plain, (r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_71])).
% 0.20/0.56  fof(c_0_91, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t175_funct_2])).
% 0.20/0.56  cnf(c_0_92, plain, (k9_relat_1(k6_relat_1(X1),X2)=X2|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_87]), c_0_67])])).
% 0.20/0.56  cnf(c_0_93, plain, (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2))=k9_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_69]), c_0_89]), c_0_68]), c_0_45])])).
% 0.20/0.56  cnf(c_0_94, plain, (r1_tarski(k10_relat_1(k6_relat_1(X1),X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_79]), c_0_45])])).
% 0.20/0.56  cnf(c_0_95, plain, (k1_setfam_1(k2_tarski(X1,X2))=k9_relat_1(k6_relat_1(X1),X2)), inference(rw,[status(thm)],[c_0_48, c_0_72])).
% 0.20/0.56  fof(c_0_96, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)&k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_91])])])).
% 0.20/0.56  cnf(c_0_97, plain, (k9_relat_1(k6_relat_1(X1),X2)=k10_relat_1(k6_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])])).
% 0.20/0.56  cnf(c_0_98, plain, (k9_relat_1(k6_relat_1(X1),X2)=k9_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_42]), c_0_48]), c_0_72])).
% 0.20/0.56  cnf(c_0_99, negated_conjecture, (k10_relat_1(esk1_0,esk3_0)!=k10_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.20/0.56  cnf(c_0_100, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k10_relat_1(k6_relat_1(k10_relat_1(X1,X3)),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_78, c_0_97])).
% 0.20/0.56  cnf(c_0_101, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.20/0.56  cnf(c_0_102, plain, (k10_relat_1(k6_relat_1(X1),X2)=k10_relat_1(k6_relat_1(X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_97]), c_0_97])).
% 0.20/0.56  cnf(c_0_103, negated_conjecture, (k10_relat_1(k6_relat_1(esk2_0),k10_relat_1(esk1_0,esk3_0))!=k10_relat_1(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_101])]), c_0_102])).
% 0.20/0.56  cnf(c_0_104, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.20/0.56  cnf(c_0_105, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_85]), c_0_104])]), ['proof']).
% 0.20/0.56  # SZS output end CNFRefutation
% 0.20/0.56  # Proof object total steps             : 106
% 0.20/0.56  # Proof object clause steps            : 71
% 0.20/0.56  # Proof object formula steps           : 35
% 0.20/0.56  # Proof object conjectures             : 8
% 0.20/0.56  # Proof object clause conjectures      : 5
% 0.20/0.56  # Proof object formula conjectures     : 3
% 0.20/0.56  # Proof object initial clauses used    : 22
% 0.20/0.56  # Proof object initial formulas used   : 17
% 0.20/0.56  # Proof object generating inferences   : 29
% 0.20/0.56  # Proof object simplifying inferences  : 73
% 0.20/0.56  # Training examples: 0 positive, 0 negative
% 0.20/0.56  # Parsed axioms                        : 17
% 0.20/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.56  # Initial clauses                      : 24
% 0.20/0.56  # Removed in clause preprocessing      : 2
% 0.20/0.56  # Initial clauses in saturation        : 22
% 0.20/0.56  # Processed clauses                    : 1812
% 0.20/0.56  # ...of these trivial                  : 21
% 0.20/0.56  # ...subsumed                          : 1449
% 0.20/0.56  # ...remaining for further processing  : 342
% 0.20/0.56  # Other redundant clauses eliminated   : 2
% 0.20/0.56  # Clauses deleted for lack of memory   : 0
% 0.20/0.56  # Backward-subsumed                    : 9
% 0.20/0.56  # Backward-rewritten                   : 147
% 0.20/0.56  # Generated clauses                    : 9243
% 0.20/0.56  # ...of the previous two non-trivial   : 6511
% 0.20/0.56  # Contextual simplify-reflections      : 3
% 0.20/0.56  # Paramodulations                      : 9241
% 0.20/0.56  # Factorizations                       : 0
% 0.20/0.56  # Equation resolutions                 : 2
% 0.20/0.56  # Propositional unsat checks           : 0
% 0.20/0.56  #    Propositional check models        : 0
% 0.20/0.56  #    Propositional check unsatisfiable : 0
% 0.20/0.56  #    Propositional clauses             : 0
% 0.20/0.56  #    Propositional clauses after purity: 0
% 0.20/0.56  #    Propositional unsat core size     : 0
% 0.20/0.56  #    Propositional preprocessing time  : 0.000
% 0.20/0.56  #    Propositional encoding time       : 0.000
% 0.20/0.56  #    Propositional solver time         : 0.000
% 0.20/0.56  #    Success case prop preproc time    : 0.000
% 0.20/0.56  #    Success case prop encoding time   : 0.000
% 0.20/0.56  #    Success case prop solver time     : 0.000
% 0.20/0.56  # Current number of processed clauses  : 163
% 0.20/0.56  #    Positive orientable unit clauses  : 24
% 0.20/0.56  #    Positive unorientable unit clauses: 2
% 0.20/0.56  #    Negative unit clauses             : 4
% 0.20/0.56  #    Non-unit-clauses                  : 133
% 0.20/0.56  # Current number of unprocessed clauses: 4507
% 0.20/0.56  # ...number of literals in the above   : 14507
% 0.20/0.56  # Current number of archived formulas  : 0
% 0.20/0.56  # Current number of archived clauses   : 179
% 0.20/0.56  # Clause-clause subsumption calls (NU) : 7524
% 0.20/0.56  # Rec. Clause-clause subsumption calls : 5917
% 0.20/0.56  # Non-unit clause-clause subsumptions  : 1259
% 0.20/0.56  # Unit Clause-clause subsumption calls : 95
% 0.20/0.56  # Rewrite failures with RHS unbound    : 0
% 0.20/0.56  # BW rewrite match attempts            : 175
% 0.20/0.56  # BW rewrite match successes           : 108
% 0.20/0.56  # Condensation attempts                : 0
% 0.20/0.56  # Condensation successes               : 0
% 0.20/0.56  # Termbank termtop insertions          : 142432
% 0.40/0.56  
% 0.40/0.56  # -------------------------------------------------
% 0.40/0.56  # User time                : 0.207 s
% 0.40/0.56  # System time              : 0.011 s
% 0.40/0.56  # Total time               : 0.218 s
% 0.40/0.56  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
