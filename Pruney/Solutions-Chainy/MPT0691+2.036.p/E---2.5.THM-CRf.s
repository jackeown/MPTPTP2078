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
% DateTime   : Thu Dec  3 10:54:46 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 157 expanded)
%              Number of clauses        :   46 (  72 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  132 ( 298 expanded)
%              Number of equality atoms :   41 (  76 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_16,plain,(
    ! [X41,X42,X43] :
      ( ~ v1_relat_1(X43)
      | k10_relat_1(k7_relat_1(X43,X41),X42) = k3_xboole_0(X41,k10_relat_1(X43,X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

fof(c_0_17,plain,(
    ! [X25,X26] : k1_setfam_1(k2_tarski(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

fof(c_0_19,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_20,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k3_xboole_0(X18,X19) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_21,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_24,plain,(
    ! [X33] :
      ( ~ v1_relat_1(X33)
      | k10_relat_1(X33,k2_relat_1(X33)) = k1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_25,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(X22,X23)
      | ~ r1_tarski(X24,X23)
      | r1_tarski(k2_xboole_0(X22,X24),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

fof(c_0_26,plain,(
    ! [X20,X21] : r1_tarski(X20,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_27,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | r1_tarski(X8,k2_xboole_0(X10,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X16,X17] : r1_tarski(k3_xboole_0(X16,X17),X16) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_30,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_31,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X27)
      | v1_relat_1(k7_relat_1(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k2_tarski(X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_36,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X40)
      | r1_tarski(k1_relat_1(k7_relat_1(X40,X39)),X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_43,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | k2_relat_1(k7_relat_1(X30,X29)) = k9_relat_1(X30,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_44,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | r1_tarski(k10_relat_1(X32,X31),k1_relat_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_45,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k10_relat_1(esk2_0,X2))) = k10_relat_1(k7_relat_1(esk2_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( k10_relat_1(esk2_0,k2_relat_1(esk2_0)) = k1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

fof(c_0_50,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k2_xboole_0(X14,X15) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_41,c_0_22])).

cnf(c_0_55,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_22]),c_0_22])).

cnf(c_0_56,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_34])).

cnf(c_0_59,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk1_0,k1_relat_1(esk2_0))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k1_relat_1(esk2_0))) = k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_34])).

cnf(c_0_63,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_64,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,X1)) = k9_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_34])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k1_relat_1(k7_relat_1(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,esk1_0),k2_relat_1(esk2_0)) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(k7_relat_1(esk2_0,X1)),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_64])])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k10_relat_1(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_48])).

cnf(c_0_72,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X1)) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_58]),c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( k2_xboole_0(X1,k1_relat_1(k7_relat_1(esk2_0,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_73]),c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:25:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.48  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.20/0.48  # and selection function SelectDiffNegLit.
% 0.20/0.48  #
% 0.20/0.48  # Preprocessing time       : 0.027 s
% 0.20/0.48  # Presaturation interreduction done
% 0.20/0.48  
% 0.20/0.48  # Proof found!
% 0.20/0.48  # SZS status Theorem
% 0.20/0.48  # SZS output start CNFRefutation
% 0.20/0.48  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 0.20/0.48  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.48  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 0.20/0.48  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.48  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.48  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.20/0.48  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.20/0.48  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.48  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.20/0.48  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.48  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.48  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.20/0.48  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 0.20/0.48  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.20/0.48  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.20/0.48  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.48  fof(c_0_16, plain, ![X41, X42, X43]:(~v1_relat_1(X43)|k10_relat_1(k7_relat_1(X43,X41),X42)=k3_xboole_0(X41,k10_relat_1(X43,X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.20/0.48  fof(c_0_17, plain, ![X25, X26]:k1_setfam_1(k2_tarski(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.48  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.20/0.48  fof(c_0_19, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.48  fof(c_0_20, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k3_xboole_0(X18,X19)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.48  cnf(c_0_21, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.48  fof(c_0_23, negated_conjecture, (v1_relat_1(esk2_0)&(r1_tarski(esk1_0,k1_relat_1(esk2_0))&~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.20/0.48  fof(c_0_24, plain, ![X33]:(~v1_relat_1(X33)|k10_relat_1(X33,k2_relat_1(X33))=k1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.20/0.48  fof(c_0_25, plain, ![X22, X23, X24]:(~r1_tarski(X22,X23)|~r1_tarski(X24,X23)|r1_tarski(k2_xboole_0(X22,X24),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.20/0.48  fof(c_0_26, plain, ![X20, X21]:r1_tarski(X20,k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.48  fof(c_0_27, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|r1_tarski(X8,k2_xboole_0(X10,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.20/0.48  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.48  fof(c_0_29, plain, ![X16, X17]:r1_tarski(k3_xboole_0(X16,X17),X16), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.48  fof(c_0_30, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.48  fof(c_0_31, plain, ![X27, X28]:(~v1_relat_1(X27)|v1_relat_1(k7_relat_1(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.20/0.48  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.48  cnf(c_0_33, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k2_tarski(X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.48  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.48  cnf(c_0_35, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.48  fof(c_0_36, plain, ![X39, X40]:(~v1_relat_1(X40)|r1_tarski(k1_relat_1(k7_relat_1(X40,X39)),X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.20/0.48  cnf(c_0_37, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.48  cnf(c_0_38, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.48  cnf(c_0_39, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.48  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.48  cnf(c_0_41, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.48  cnf(c_0_42, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.48  fof(c_0_43, plain, ![X29, X30]:(~v1_relat_1(X30)|k2_relat_1(k7_relat_1(X30,X29))=k9_relat_1(X30,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.20/0.48  fof(c_0_44, plain, ![X31, X32]:(~v1_relat_1(X32)|r1_tarski(k10_relat_1(X32,X31),k1_relat_1(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.20/0.48  cnf(c_0_45, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.48  cnf(c_0_46, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_22])).
% 0.20/0.48  cnf(c_0_47, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.48  cnf(c_0_48, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k10_relat_1(esk2_0,X2)))=k10_relat_1(k7_relat_1(esk2_0,X1),X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.48  cnf(c_0_49, negated_conjecture, (k10_relat_1(esk2_0,k2_relat_1(esk2_0))=k1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.20/0.48  fof(c_0_50, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k2_xboole_0(X14,X15)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.48  cnf(c_0_51, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.48  cnf(c_0_52, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.48  cnf(c_0_53, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.48  cnf(c_0_54, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_41, c_0_22])).
% 0.20/0.48  cnf(c_0_55, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_22]), c_0_22])).
% 0.20/0.48  cnf(c_0_56, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.48  cnf(c_0_57, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.48  cnf(c_0_58, negated_conjecture, (v1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_45, c_0_34])).
% 0.20/0.48  cnf(c_0_59, negated_conjecture, (k1_setfam_1(k2_tarski(esk1_0,k1_relat_1(esk2_0)))=esk1_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.48  cnf(c_0_60, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k1_relat_1(esk2_0)))=k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.48  cnf(c_0_61, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.48  cnf(c_0_62, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),X1)), inference(spm,[status(thm)],[c_0_51, c_0_34])).
% 0.20/0.48  cnf(c_0_63, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.48  cnf(c_0_64, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.48  cnf(c_0_65, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.48  cnf(c_0_66, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,X1))=k9_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_56, c_0_34])).
% 0.20/0.48  cnf(c_0_67, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k1_relat_1(k7_relat_1(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.48  cnf(c_0_68, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,esk1_0),k2_relat_1(esk2_0))=esk1_0), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.48  cnf(c_0_69, negated_conjecture, (k2_xboole_0(k1_relat_1(k7_relat_1(esk2_0,X1)),X1)=X1), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.48  cnf(c_0_70, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_64])])).
% 0.20/0.48  cnf(c_0_71, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k10_relat_1(esk2_0,X2))), inference(spm,[status(thm)],[c_0_65, c_0_48])).
% 0.20/0.48  cnf(c_0_72, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X1))=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_58]), c_0_66])).
% 0.20/0.48  cnf(c_0_73, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.48  cnf(c_0_74, negated_conjecture, (k2_xboole_0(X1,k1_relat_1(k7_relat_1(esk2_0,X1)))=X1), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.48  cnf(c_0_75, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.48  cnf(c_0_76, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk1_0))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_73]), c_0_74])).
% 0.20/0.48  cnf(c_0_77, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.48  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), ['proof']).
% 0.20/0.48  # SZS output end CNFRefutation
% 0.20/0.48  # Proof object total steps             : 79
% 0.20/0.48  # Proof object clause steps            : 46
% 0.20/0.48  # Proof object formula steps           : 33
% 0.20/0.48  # Proof object conjectures             : 23
% 0.20/0.48  # Proof object clause conjectures      : 20
% 0.20/0.48  # Proof object formula conjectures     : 3
% 0.20/0.48  # Proof object initial clauses used    : 19
% 0.20/0.48  # Proof object initial formulas used   : 16
% 0.20/0.48  # Proof object generating inferences   : 20
% 0.20/0.48  # Proof object simplifying inferences  : 13
% 0.20/0.48  # Training examples: 0 positive, 0 negative
% 0.20/0.48  # Parsed axioms                        : 19
% 0.20/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.48  # Initial clauses                      : 23
% 0.20/0.48  # Removed in clause preprocessing      : 1
% 0.20/0.48  # Initial clauses in saturation        : 22
% 0.20/0.48  # Processed clauses                    : 1368
% 0.20/0.48  # ...of these trivial                  : 178
% 0.20/0.48  # ...subsumed                          : 755
% 0.20/0.48  # ...remaining for further processing  : 435
% 0.20/0.48  # Other redundant clauses eliminated   : 2
% 0.20/0.48  # Clauses deleted for lack of memory   : 0
% 0.20/0.48  # Backward-subsumed                    : 3
% 0.20/0.48  # Backward-rewritten                   : 62
% 0.20/0.48  # Generated clauses                    : 8764
% 0.20/0.48  # ...of the previous two non-trivial   : 5876
% 0.20/0.48  # Contextual simplify-reflections      : 0
% 0.20/0.48  # Paramodulations                      : 8762
% 0.20/0.48  # Factorizations                       : 0
% 0.20/0.48  # Equation resolutions                 : 2
% 0.20/0.48  # Propositional unsat checks           : 0
% 0.20/0.48  #    Propositional check models        : 0
% 0.20/0.48  #    Propositional check unsatisfiable : 0
% 0.20/0.48  #    Propositional clauses             : 0
% 0.20/0.48  #    Propositional clauses after purity: 0
% 0.20/0.48  #    Propositional unsat core size     : 0
% 0.20/0.48  #    Propositional preprocessing time  : 0.000
% 0.20/0.48  #    Propositional encoding time       : 0.000
% 0.20/0.48  #    Propositional solver time         : 0.000
% 0.20/0.48  #    Success case prop preproc time    : 0.000
% 0.20/0.48  #    Success case prop encoding time   : 0.000
% 0.20/0.48  #    Success case prop solver time     : 0.000
% 0.20/0.48  # Current number of processed clauses  : 347
% 0.20/0.48  #    Positive orientable unit clauses  : 199
% 0.20/0.48  #    Positive unorientable unit clauses: 2
% 0.20/0.48  #    Negative unit clauses             : 1
% 0.20/0.48  #    Non-unit-clauses                  : 145
% 0.20/0.48  # Current number of unprocessed clauses: 4427
% 0.20/0.48  # ...number of literals in the above   : 5549
% 0.20/0.48  # Current number of archived formulas  : 0
% 0.20/0.48  # Current number of archived clauses   : 87
% 0.20/0.48  # Clause-clause subsumption calls (NU) : 8410
% 0.20/0.48  # Rec. Clause-clause subsumption calls : 7101
% 0.20/0.48  # Non-unit clause-clause subsumptions  : 758
% 0.20/0.48  # Unit Clause-clause subsumption calls : 110
% 0.20/0.48  # Rewrite failures with RHS unbound    : 0
% 0.20/0.48  # BW rewrite match attempts            : 472
% 0.20/0.48  # BW rewrite match successes           : 122
% 0.20/0.48  # Condensation attempts                : 0
% 0.20/0.48  # Condensation successes               : 0
% 0.20/0.48  # Termbank termtop insertions          : 115560
% 0.20/0.48  
% 0.20/0.48  # -------------------------------------------------
% 0.20/0.48  # User time                : 0.138 s
% 0.20/0.48  # System time              : 0.006 s
% 0.20/0.48  # Total time               : 0.144 s
% 0.20/0.48  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
