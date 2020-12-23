%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:14 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 277 expanded)
%              Number of clauses        :   58 ( 127 expanded)
%              Number of leaves         :   24 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  193 ( 480 expanded)
%              Number of equality atoms :   61 ( 185 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t158_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
          & r1_tarski(X1,k2_relat_1(X3)) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t172_relat_1,axiom,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t148_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_24,plain,(
    ! [X31,X32] : k1_setfam_1(k2_tarski(X31,X32)) = k3_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_25,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_29,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(k2_xboole_0(X10,X11),X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_30,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k2_xboole_0(X13,X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
            & r1_tarski(X1,k2_relat_1(X3)) )
         => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t158_funct_1])).

fof(c_0_32,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(k4_xboole_0(X24,X25),X26)
      | r1_tarski(X24,k2_xboole_0(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))
    & r1_tarski(esk1_0,k2_relat_1(esk3_0))
    & ~ r1_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk1_0,k2_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_42,plain,(
    ! [X15,X16] : r1_tarski(k4_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_43,plain,(
    ! [X40] :
      ( v1_relat_1(k6_relat_1(X40))
      & v1_funct_1(k6_relat_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_44,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,k4_xboole_0(X18,X17))
      | X17 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

fof(c_0_45,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,k2_xboole_0(X22,X23))
      | r1_tarski(k4_xboole_0(X21,X22),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X3) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk3_0))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_49,plain,(
    ! [X41,X42,X43] :
      ( ~ v1_relat_1(X43)
      | k10_relat_1(k7_relat_1(X43,X41),X42) = k3_xboole_0(X41,k10_relat_1(X43,X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

fof(c_0_50,plain,(
    ! [X20] :
      ( ~ r1_tarski(X20,k1_xboole_0)
      | X20 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_51,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | r1_tarski(k7_relat_1(X39,X38),X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_52,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_relat_1(esk3_0)))
    | ~ r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),esk1_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X1) ),
    inference(rw,[status(thm)],[c_0_48,c_0_39])).

fof(c_0_58,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_59,plain,(
    ! [X19] : k4_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_60,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_61,plain,(
    ! [X37] : k10_relat_1(k1_xboole_0,X37) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t172_relat_1])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_64,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_65,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_39])).

cnf(c_0_67,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_39])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(X1,k2_relat_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_60,c_0_34])).

cnf(c_0_72,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

fof(c_0_74,plain,(
    ! [X46,X47] :
      ( ~ v1_relat_1(X47)
      | ~ v1_funct_1(X47)
      | k9_relat_1(X47,k10_relat_1(X47,X46)) = k3_xboole_0(X46,k9_relat_1(X47,k1_relat_1(X47))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).

cnf(c_0_75,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))))))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(k2_relat_1(esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[c_0_70,c_0_39])).

cnf(c_0_79,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_72]),c_0_64])])).

cnf(c_0_80,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_81,plain,(
    ! [X33] :
      ( ~ v1_relat_1(X33)
      | k9_relat_1(X33,k1_relat_1(X33)) = k2_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_82,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))))) = k1_setfam_1(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_34]),c_0_39]),c_0_39])).

cnf(c_0_83,negated_conjecture,
    ( k5_xboole_0(esk1_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k2_relat_1(esk3_0)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_80,c_0_34])).

cnf(c_0_86,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

fof(c_0_87,plain,(
    ! [X44,X45] :
      ( ~ v1_relat_1(X45)
      | ~ v1_funct_1(X45)
      | r1_tarski(k9_relat_1(X45,k10_relat_1(X45,X44)),X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_88,plain,(
    ! [X34,X35,X36] :
      ( ~ v1_relat_1(X36)
      | ~ r1_tarski(X34,X35)
      | r1_tarski(k9_relat_1(X36,X34),k9_relat_1(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_89,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k2_relat_1(esk3_0))) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_79]),c_0_84])).

cnf(c_0_90,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(X2))) = k9_relat_1(X2,k10_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_92,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_93,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_94,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91]),c_0_92])])).

fof(c_0_96,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(esk1_0,k9_relat_1(esk3_0,X1))
    | ~ r1_tarski(k10_relat_1(esk3_0,esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_92])])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_100,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_91]),c_0_92])])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk3_0,esk2_0))
    | ~ r1_tarski(X1,k10_relat_1(esk3_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_99])).

cnf(c_0_103,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103])]),c_0_104]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:05:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.028 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.41  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.20/0.41  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.41  fof(t158_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 0.20/0.41  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.20/0.41  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.41  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.20/0.41  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 0.20/0.41  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.20/0.41  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 0.20/0.41  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.20/0.41  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 0.20/0.41  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.20/0.41  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.41  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.41  fof(t172_relat_1, axiom, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 0.20/0.41  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.41  fof(t148_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 0.20/0.41  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.20/0.41  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.20/0.41  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(c_0_24, plain, ![X31, X32]:k1_setfam_1(k2_tarski(X31,X32))=k3_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.41  fof(c_0_25, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.41  fof(c_0_26, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.41  cnf(c_0_27, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  fof(c_0_29, plain, ![X10, X11, X12]:(~r1_tarski(k2_xboole_0(X10,X11),X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.20/0.41  fof(c_0_30, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k2_xboole_0(X13,X14)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.41  fof(c_0_31, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t158_funct_1])).
% 0.20/0.41  fof(c_0_32, plain, ![X24, X25, X26]:(~r1_tarski(k4_xboole_0(X24,X25),X26)|r1_tarski(X24,k2_xboole_0(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.20/0.41  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_34, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.41  cnf(c_0_35, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.41  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.41  fof(c_0_37, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))&r1_tarski(esk1_0,k2_relat_1(esk3_0)))&~r1_tarski(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.20/0.41  cnf(c_0_38, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.41  cnf(c_0_39, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.41  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (r1_tarski(esk1_0,k2_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.41  fof(c_0_42, plain, ![X15, X16]:r1_tarski(k4_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.41  fof(c_0_43, plain, ![X40]:(v1_relat_1(k6_relat_1(X40))&v1_funct_1(k6_relat_1(X40))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.20/0.41  fof(c_0_44, plain, ![X17, X18]:(~r1_tarski(X17,k4_xboole_0(X18,X17))|X17=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 0.20/0.41  fof(c_0_45, plain, ![X21, X22, X23]:(~r1_tarski(X21,k2_xboole_0(X22,X23))|r1_tarski(k4_xboole_0(X21,X22),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.20/0.41  cnf(c_0_46, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X3)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (r1_tarski(X1,k2_relat_1(esk3_0))|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.41  cnf(c_0_48, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  fof(c_0_49, plain, ![X41, X42, X43]:(~v1_relat_1(X43)|k10_relat_1(k7_relat_1(X43,X41),X42)=k3_xboole_0(X41,k10_relat_1(X43,X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.20/0.41  fof(c_0_50, plain, ![X20]:(~r1_tarski(X20,k1_xboole_0)|X20=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.20/0.41  fof(c_0_51, plain, ![X38, X39]:(~v1_relat_1(X39)|r1_tarski(k7_relat_1(X39,X38),X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.20/0.41  cnf(c_0_52, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.41  cnf(c_0_53, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.20/0.41  cnf(c_0_54, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.41  cnf(c_0_55, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (r1_tarski(X1,k2_xboole_0(X2,k2_relat_1(esk3_0)))|~r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),esk1_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.41  cnf(c_0_57, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X1)), inference(rw,[status(thm)],[c_0_48, c_0_39])).
% 0.20/0.41  fof(c_0_58, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.41  fof(c_0_59, plain, ![X19]:k4_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.41  cnf(c_0_60, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.41  fof(c_0_61, plain, ![X37]:k10_relat_1(k1_xboole_0,X37)=k1_xboole_0, inference(variable_rename,[status(thm)],[t172_relat_1])).
% 0.20/0.41  cnf(c_0_62, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.41  cnf(c_0_63, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.41  cnf(c_0_64, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.41  fof(c_0_65, plain, ![X27, X28]:k4_xboole_0(X27,k4_xboole_0(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.41  cnf(c_0_66, plain, (X1=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X1))))), inference(rw,[status(thm)],[c_0_54, c_0_39])).
% 0.20/0.41  cnf(c_0_67, plain, (r1_tarski(k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_55, c_0_39])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(X1,k2_relat_1(esk3_0)))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.41  cnf(c_0_69, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.41  cnf(c_0_70, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.41  cnf(c_0_71, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_60, c_0_34])).
% 0.20/0.41  cnf(c_0_72, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.41  cnf(c_0_73, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 0.20/0.41  fof(c_0_74, plain, ![X46, X47]:(~v1_relat_1(X47)|~v1_funct_1(X47)|k9_relat_1(X47,k10_relat_1(X47,X46))=k3_xboole_0(X46,k9_relat_1(X47,k1_relat_1(X47)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).
% 0.20/0.41  cnf(c_0_75, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.41  cnf(c_0_76, plain, (k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))=k1_xboole_0|~r1_tarski(X1,k2_xboole_0(X2,k5_xboole_0(X3,k1_setfam_1(k1_enumset1(X3,X3,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))))))))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.41  cnf(c_0_77, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(k2_relat_1(esk3_0),X1))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.41  cnf(c_0_78, plain, (k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[c_0_70, c_0_39])).
% 0.20/0.41  cnf(c_0_79, plain, (k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_72]), c_0_64])])).
% 0.20/0.41  cnf(c_0_80, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.41  fof(c_0_81, plain, ![X33]:(~v1_relat_1(X33)|k9_relat_1(X33,k1_relat_1(X33))=k2_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.20/0.41  cnf(c_0_82, plain, (k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))))))=k1_setfam_1(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_34]), c_0_39]), c_0_39])).
% 0.20/0.41  cnf(c_0_83, negated_conjecture, (k5_xboole_0(esk1_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k2_relat_1(esk3_0))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.41  cnf(c_0_84, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_78, c_0_79])).
% 0.20/0.41  cnf(c_0_85, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[c_0_80, c_0_34])).
% 0.20/0.41  cnf(c_0_86, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.41  fof(c_0_87, plain, ![X44, X45]:(~v1_relat_1(X45)|~v1_funct_1(X45)|r1_tarski(k9_relat_1(X45,k10_relat_1(X45,X44)),X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.20/0.41  fof(c_0_88, plain, ![X34, X35, X36]:(~v1_relat_1(X36)|(~r1_tarski(X34,X35)|r1_tarski(k9_relat_1(X36,X34),k9_relat_1(X36,X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.20/0.41  cnf(c_0_89, negated_conjecture, (k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k2_relat_1(esk3_0)))=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_79]), c_0_84])).
% 0.20/0.41  cnf(c_0_90, plain, (k1_setfam_1(k1_enumset1(X1,X1,k2_relat_1(X2)))=k9_relat_1(X2,k10_relat_1(X2,X1))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.20/0.41  cnf(c_0_91, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.41  cnf(c_0_92, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.41  cnf(c_0_93, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.20/0.41  cnf(c_0_94, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.20/0.41  cnf(c_0_95, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91]), c_0_92])])).
% 0.20/0.41  fof(c_0_96, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  cnf(c_0_97, plain, (r1_tarski(X1,X2)|~v1_funct_1(X3)|~v1_relat_1(X3)|~r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,X2)))), inference(spm,[status(thm)],[c_0_40, c_0_93])).
% 0.20/0.41  cnf(c_0_98, negated_conjecture, (r1_tarski(esk1_0,k9_relat_1(esk3_0,X1))|~r1_tarski(k10_relat_1(esk3_0,esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_92])])).
% 0.20/0.41  cnf(c_0_99, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.41  cnf(c_0_100, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.20/0.41  cnf(c_0_101, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_91]), c_0_92])])).
% 0.20/0.41  cnf(c_0_102, negated_conjecture, (r1_tarski(X1,k10_relat_1(esk3_0,esk2_0))|~r1_tarski(X1,k10_relat_1(esk3_0,esk1_0))), inference(spm,[status(thm)],[c_0_40, c_0_99])).
% 0.20/0.41  cnf(c_0_103, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_100])).
% 0.20/0.41  cnf(c_0_104, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.41  cnf(c_0_105, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103])]), c_0_104]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 106
% 0.20/0.41  # Proof object clause steps            : 58
% 0.20/0.41  # Proof object formula steps           : 48
% 0.20/0.41  # Proof object conjectures             : 19
% 0.20/0.41  # Proof object clause conjectures      : 16
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 28
% 0.20/0.41  # Proof object initial formulas used   : 24
% 0.20/0.41  # Proof object generating inferences   : 18
% 0.20/0.41  # Proof object simplifying inferences  : 33
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 24
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 31
% 0.20/0.41  # Removed in clause preprocessing      : 3
% 0.20/0.41  # Initial clauses in saturation        : 28
% 0.20/0.41  # Processed clauses                    : 464
% 0.20/0.41  # ...of these trivial                  : 22
% 0.20/0.41  # ...subsumed                          : 228
% 0.20/0.41  # ...remaining for further processing  : 214
% 0.20/0.41  # Other redundant clauses eliminated   : 2
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 1
% 0.20/0.41  # Backward-rewritten                   : 13
% 0.20/0.41  # Generated clauses                    : 1269
% 0.20/0.41  # ...of the previous two non-trivial   : 1049
% 0.20/0.41  # Contextual simplify-reflections      : 0
% 0.20/0.41  # Paramodulations                      : 1267
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 2
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 171
% 0.20/0.41  #    Positive orientable unit clauses  : 38
% 0.20/0.41  #    Positive unorientable unit clauses: 1
% 0.20/0.41  #    Negative unit clauses             : 1
% 0.20/0.41  #    Non-unit-clauses                  : 131
% 0.20/0.41  # Current number of unprocessed clauses: 622
% 0.20/0.41  # ...number of literals in the above   : 1799
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 44
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 5215
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 4704
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 229
% 0.20/0.41  # Unit Clause-clause subsumption calls : 3
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 44
% 0.20/0.41  # BW rewrite match successes           : 18
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 17324
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.056 s
% 0.20/0.41  # System time              : 0.006 s
% 0.20/0.41  # Total time               : 0.061 s
% 0.20/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
