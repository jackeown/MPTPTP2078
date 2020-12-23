%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:42 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 525 expanded)
%              Number of clauses        :   66 ( 245 expanded)
%              Number of leaves         :   17 ( 133 expanded)
%              Depth                    :   17
%              Number of atoms          :  161 ( 855 expanded)
%              Number of equality atoms :   57 ( 340 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(c_0_17,plain,(
    ! [X18,X19] : r1_tarski(X18,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_18,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_19,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,k2_xboole_0(X14,X15))
      | r1_tarski(k4_xboole_0(X13,X14),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_25,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_26,plain,(
    ! [X22,X23] : k1_setfam_1(k2_tarski(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X20,X21] : k2_tarski(X20,X21) = k2_tarski(X21,X20) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_32,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | k1_relat_1(k7_relat_1(X32,X31)) = k3_xboole_0(k1_relat_1(X32),X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

fof(c_0_34,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_38,c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_40])).

fof(c_0_46,plain,(
    ! [X12] : k4_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(esk2_0),k4_xboole_0(k1_relat_1(esk2_0),X1)) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_36])).

cnf(c_0_51,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_45])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(k1_relat_1(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(esk2_0,X2))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_56,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

fof(c_0_58,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(k1_relat_1(esk2_0),X2))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_45])).

cnf(c_0_61,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_62,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_24])])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(X1,k1_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_48])).

fof(c_0_64,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | v1_relat_1(k7_relat_1(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),k2_xboole_0(k1_relat_1(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_67,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X27)
      | ~ r1_tarski(X28,X29)
      | k9_relat_1(k7_relat_1(X27,X29),X28) = k9_relat_1(X27,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

cnf(c_0_68,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,X1),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_63])).

fof(c_0_70,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | k9_relat_1(X26,k1_relat_1(X26)) = k2_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_71,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),k1_relat_1(esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_66])).

cnf(c_0_74,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(esk1_0,X1),k1_relat_1(esk2_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

fof(c_0_76,plain,(
    ! [X33,X34,X35] :
      ( ~ v1_relat_1(X35)
      | k10_relat_1(k7_relat_1(X35,X33),X34) = k3_xboole_0(X33,k10_relat_1(X35,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_77,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_44])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),k1_relat_1(esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_80,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_45])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_42])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk1_0,X1),k1_relat_1(esk2_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_75]),c_0_65])])).

cnf(c_0_83,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

fof(c_0_84,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | k10_relat_1(X30,k2_relat_1(X30)) = k1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_85,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk2_0,X1),k1_relat_1(k7_relat_1(esk2_0,X1))) = k2_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0)))) = k1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_79]),c_0_52]),c_0_37]),c_0_36]),c_0_50])).

cnf(c_0_87,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk2_0,X1),X1) = k9_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_44])).

cnf(c_0_88,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k4_xboole_0(esk1_0,X1))) = k4_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_50]),c_0_52])).

cnf(c_0_89,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k2_tarski(X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_83,c_0_30])).

cnf(c_0_90,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0)))) = k9_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_52])).

cnf(c_0_93,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_42])).

cnf(c_0_94,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k10_relat_1(esk2_0,X2))) = k10_relat_1(k7_relat_1(esk2_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_44])).

cnf(c_0_95,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(k7_relat_1(esk2_0,X1))) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_78])).

cnf(c_0_96,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,esk1_0)) = k9_relat_1(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92]),c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k10_relat_1(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:56:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.19/0.40  # and selection function SelectDiffNegLit.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.028 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.40  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.40  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.19/0.40  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.40  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.40  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.19/0.40  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.40  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.19/0.40  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.19/0.40  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.19/0.40  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.19/0.40  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.19/0.40  fof(c_0_17, plain, ![X18, X19]:r1_tarski(X18,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.40  fof(c_0_18, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.40  fof(c_0_19, plain, ![X13, X14, X15]:(~r1_tarski(X13,k2_xboole_0(X14,X15))|r1_tarski(k4_xboole_0(X13,X14),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.19/0.40  cnf(c_0_20, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  fof(c_0_22, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X9,X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.40  cnf(c_0_23, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_24, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.40  fof(c_0_25, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.40  fof(c_0_26, plain, ![X22, X23]:k1_setfam_1(k2_tarski(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.40  cnf(c_0_27, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_28, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.40  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  cnf(c_0_30, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  fof(c_0_31, plain, ![X20, X21]:k2_tarski(X20,X21)=k2_tarski(X21,X20), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.40  fof(c_0_32, plain, ![X31, X32]:(~v1_relat_1(X32)|k1_relat_1(k7_relat_1(X32,X31))=k3_xboole_0(k1_relat_1(X32),X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.19/0.40  fof(c_0_33, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.19/0.40  fof(c_0_34, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.40  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.40  cnf(c_0_37, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_38, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.40  fof(c_0_39, negated_conjecture, (v1_relat_1(esk2_0)&(r1_tarski(esk1_0,k1_relat_1(esk2_0))&~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 0.19/0.40  cnf(c_0_40, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.40  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.40  cnf(c_0_43, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_tarski(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_38, c_0_30])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.40  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_40])).
% 0.19/0.40  fof(c_0_46, plain, ![X12]:k4_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.40  cnf(c_0_47, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_20])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.40  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.40  cnf(c_0_50, negated_conjecture, (k4_xboole_0(k1_relat_1(esk2_0),k4_xboole_0(k1_relat_1(esk2_0),X1))=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_36])).
% 0.19/0.40  cnf(c_0_51, plain, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X1),X2)), inference(spm,[status(thm)],[c_0_23, c_0_45])).
% 0.19/0.40  cnf(c_0_52, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.40  cnf(c_0_53, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(k1_relat_1(esk2_0),X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.40  cnf(c_0_54, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_relat_1(k7_relat_1(esk2_0,X2)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.40  cnf(c_0_55, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_56, plain, (r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.40  cnf(c_0_57, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.19/0.40  fof(c_0_58, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (r1_tarski(X1,k2_xboole_0(k1_relat_1(esk2_0),X2))|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_27, c_0_53])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),X1)), inference(spm,[status(thm)],[c_0_54, c_0_45])).
% 0.19/0.40  cnf(c_0_61, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.19/0.40  cnf(c_0_62, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_24])])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(X1,k1_relat_1(esk2_0)))), inference(spm,[status(thm)],[c_0_57, c_0_48])).
% 0.19/0.40  fof(c_0_64, plain, ![X24, X25]:(~v1_relat_1(X24)|v1_relat_1(k7_relat_1(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.19/0.40  cnf(c_0_65, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),k2_xboole_0(k1_relat_1(esk2_0),X1))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.40  fof(c_0_67, plain, ![X27, X28, X29]:(~v1_relat_1(X27)|(~r1_tarski(X28,X29)|k9_relat_1(k7_relat_1(X27,X29),X28)=k9_relat_1(X27,X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.19/0.40  cnf(c_0_68, plain, (r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,X1),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_63])).
% 0.19/0.40  fof(c_0_70, plain, ![X26]:(~v1_relat_1(X26)|k9_relat_1(X26,k1_relat_1(X26))=k2_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.19/0.40  cnf(c_0_71, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.40  cnf(c_0_72, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_65])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, (r1_tarski(k4_xboole_0(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),k1_relat_1(esk2_0)),X1)), inference(spm,[status(thm)],[c_0_23, c_0_66])).
% 0.19/0.40  cnf(c_0_74, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.40  cnf(c_0_75, negated_conjecture, (r1_tarski(k4_xboole_0(k4_xboole_0(esk1_0,X1),k1_relat_1(esk2_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.40  fof(c_0_76, plain, ![X33, X34, X35]:(~v1_relat_1(X35)|k10_relat_1(k7_relat_1(X35,X33),X34)=k3_xboole_0(X33,k10_relat_1(X35,X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.19/0.40  cnf(c_0_77, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, (v1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_71, c_0_44])).
% 0.19/0.40  cnf(c_0_79, negated_conjecture, (k4_xboole_0(k1_relat_1(k7_relat_1(esk2_0,esk1_0)),k1_relat_1(esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.40  cnf(c_0_80, plain, (k9_relat_1(k7_relat_1(X1,X2),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_74, c_0_45])).
% 0.19/0.40  cnf(c_0_81, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_36, c_0_42])).
% 0.19/0.40  cnf(c_0_82, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk1_0,X1),k1_relat_1(esk2_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_75]), c_0_65])])).
% 0.19/0.40  cnf(c_0_83, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.40  fof(c_0_84, plain, ![X30]:(~v1_relat_1(X30)|k10_relat_1(X30,k2_relat_1(X30))=k1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.19/0.40  cnf(c_0_85, negated_conjecture, (k9_relat_1(k7_relat_1(esk2_0,X1),k1_relat_1(k7_relat_1(esk2_0,X1)))=k2_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.40  cnf(c_0_86, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0))))=k1_relat_1(k7_relat_1(esk2_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_79]), c_0_52]), c_0_37]), c_0_36]), c_0_50])).
% 0.19/0.40  cnf(c_0_87, negated_conjecture, (k9_relat_1(k7_relat_1(esk2_0,X1),X1)=k9_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_80, c_0_44])).
% 0.19/0.40  cnf(c_0_88, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k4_xboole_0(esk1_0,X1)))=k4_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_50]), c_0_52])).
% 0.19/0.40  cnf(c_0_89, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k2_tarski(X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_83, c_0_30])).
% 0.19/0.40  cnf(c_0_90, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.19/0.40  cnf(c_0_91, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0))))=k9_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk2_0,esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87])).
% 0.19/0.40  cnf(c_0_92, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,esk1_0))=esk1_0), inference(spm,[status(thm)],[c_0_88, c_0_52])).
% 0.19/0.40  cnf(c_0_93, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_28, c_0_42])).
% 0.19/0.40  cnf(c_0_94, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k10_relat_1(esk2_0,X2)))=k10_relat_1(k7_relat_1(esk2_0,X1),X2)), inference(spm,[status(thm)],[c_0_89, c_0_44])).
% 0.19/0.40  cnf(c_0_95, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,X1),k2_relat_1(k7_relat_1(esk2_0,X1)))=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_90, c_0_78])).
% 0.19/0.40  cnf(c_0_96, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,esk1_0))=k9_relat_1(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92]), c_0_92])).
% 0.19/0.40  cnf(c_0_97, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk2_0,X1),X2),k10_relat_1(esk2_0,X2))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.19/0.40  cnf(c_0_98, negated_conjecture, (k10_relat_1(k7_relat_1(esk2_0,esk1_0),k9_relat_1(esk2_0,esk1_0))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_92])).
% 0.19/0.40  cnf(c_0_99, negated_conjecture, (~r1_tarski(esk1_0,k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.40  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 101
% 0.19/0.40  # Proof object clause steps            : 66
% 0.19/0.40  # Proof object formula steps           : 35
% 0.19/0.40  # Proof object conjectures             : 31
% 0.19/0.40  # Proof object clause conjectures      : 28
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 20
% 0.19/0.40  # Proof object initial formulas used   : 17
% 0.19/0.40  # Proof object generating inferences   : 41
% 0.19/0.40  # Proof object simplifying inferences  : 20
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 17
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 21
% 0.19/0.40  # Removed in clause preprocessing      : 1
% 0.19/0.40  # Initial clauses in saturation        : 20
% 0.19/0.40  # Processed clauses                    : 618
% 0.19/0.40  # ...of these trivial                  : 75
% 0.19/0.40  # ...subsumed                          : 297
% 0.19/0.40  # ...remaining for further processing  : 246
% 0.19/0.40  # Other redundant clauses eliminated   : 2
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 4
% 0.19/0.40  # Backward-rewritten                   : 22
% 0.19/0.40  # Generated clauses                    : 3013
% 0.19/0.40  # ...of the previous two non-trivial   : 2291
% 0.19/0.40  # Contextual simplify-reflections      : 0
% 0.19/0.40  # Paramodulations                      : 3011
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 2
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 199
% 0.19/0.40  #    Positive orientable unit clauses  : 107
% 0.19/0.40  #    Positive unorientable unit clauses: 5
% 0.19/0.40  #    Negative unit clauses             : 1
% 0.19/0.40  #    Non-unit-clauses                  : 86
% 0.19/0.40  # Current number of unprocessed clauses: 1661
% 0.19/0.40  # ...number of literals in the above   : 1927
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 46
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 3992
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 2554
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 298
% 0.19/0.40  # Unit Clause-clause subsumption calls : 68
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 163
% 0.19/0.40  # BW rewrite match successes           : 36
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 30496
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.066 s
% 0.19/0.41  # System time              : 0.005 s
% 0.19/0.41  # Total time               : 0.071 s
% 0.19/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
