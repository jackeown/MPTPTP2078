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
% DateTime   : Thu Dec  3 10:54:44 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 396 expanded)
%              Number of clauses        :   60 ( 177 expanded)
%              Number of leaves         :   14 (  94 expanded)
%              Depth                    :   17
%              Number of atoms          :  149 ( 809 expanded)
%              Number of equality atoms :   49 ( 140 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

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

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

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

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

fof(c_0_15,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | v1_relat_1(k7_relat_1(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk2_0,k1_relat_1(esk3_0))
    & ~ r1_tarski(esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | r1_tarski(k10_relat_1(X29,X28),k1_relat_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_18,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | k2_xboole_0(X17,X18) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_23,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ r1_tarski(X33,k1_relat_1(X34))
      | k1_relat_1(k7_relat_1(X34,X33)) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_24,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(k2_xboole_0(X14,X15),X16)
      | r1_tarski(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),X2),k1_relat_1(k7_relat_1(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | r1_tarski(k1_relat_1(k7_relat_1(X32,X31)),X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_28,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k2_xboole_0(k10_relat_1(k7_relat_1(esk3_0,X1),X2),k1_relat_1(k7_relat_1(esk3_0,X1))) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | k2_relat_1(k7_relat_1(X27,X26)) = k9_relat_1(X27,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,X1)) = X1
    | ~ r1_tarski(X1,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_35,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X37)
      | k10_relat_1(k7_relat_1(X37,X35),X36) = k3_xboole_0(X35,k10_relat_1(X37,X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),X2),X3)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_19])).

fof(c_0_38,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | k10_relat_1(X30,k2_relat_1(X30)) = k1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_39,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k3_xboole_0(X19,X20) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_41,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_42,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_43,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)) = X2
    | ~ r1_tarski(X2,k1_relat_1(k7_relat_1(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22])).

fof(c_0_45,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_22])).

cnf(c_0_49,negated_conjecture,
    ( k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_22])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk3_0,esk2_0),X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_41])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(X1,k10_relat_1(k7_relat_1(esk3_0,X2),X3)) = k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,X2),X1),X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_22])).

cnf(c_0_54,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),X1)) = X1
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_41])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( k2_xboole_0(k10_relat_1(k7_relat_1(esk3_0,X1),X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_25,c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(X1,k10_relat_1(esk3_0,X2)) = k10_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_19])).

cnf(c_0_58,negated_conjecture,
    ( k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k9_relat_1(k7_relat_1(esk3_0,X1),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),esk2_0),X1) = k10_relat_1(k7_relat_1(esk3_0,esk2_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_37]),c_0_41]),c_0_41])).

fof(c_0_61,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,X22)
      | ~ r1_tarski(X23,X22)
      | r1_tarski(k2_xboole_0(X21,X23),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( k3_xboole_0(k10_relat_1(esk3_0,X1),X2) = k10_relat_1(k7_relat_1(esk3_0,X2),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk3_0,esk2_0),k9_relat_1(k7_relat_1(esk3_0,esk2_0),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_66,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2)),X3),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_46])).

cnf(c_0_69,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2)),X3) = k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3),k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_48])).

cnf(c_0_71,negated_conjecture,
    ( k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),X1),k9_relat_1(k7_relat_1(esk3_0,esk2_0),esk2_0)) = k3_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_65])).

cnf(c_0_72,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)),X3),X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk2_0),k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),X1))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_76,plain,
    ( r1_tarski(k2_xboole_0(k2_xboole_0(X1,X2),X1),k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_62])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_50,c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_58])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk3_0,esk2_0),X1),k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),k10_relat_1(esk3_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_64])).

cnf(c_0_80,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X1)) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_22]),c_0_75])).

cnf(c_0_81,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_76]),c_0_52]),c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_25,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_41])).

cnf(c_0_84,negated_conjecture,
    ( k2_xboole_0(X1,k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)))) = X1 ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_22])).

cnf(c_0_86,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_83]),c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:18:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.54/1.76  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 1.54/1.76  # and selection function SelectSmallestOrientable.
% 1.54/1.76  #
% 1.54/1.76  # Preprocessing time       : 0.027 s
% 1.54/1.76  # Presaturation interreduction done
% 1.54/1.76  
% 1.54/1.76  # Proof found!
% 1.54/1.76  # SZS status Theorem
% 1.54/1.76  # SZS output start CNFRefutation
% 1.54/1.76  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 1.54/1.76  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.54/1.76  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 1.54/1.76  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.54/1.76  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 1.54/1.76  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.54/1.76  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 1.54/1.76  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.54/1.76  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 1.54/1.76  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 1.54/1.76  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.54/1.76  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.54/1.76  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.54/1.76  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.54/1.76  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 1.54/1.76  fof(c_0_15, plain, ![X24, X25]:(~v1_relat_1(X24)|v1_relat_1(k7_relat_1(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 1.54/1.76  fof(c_0_16, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk2_0,k1_relat_1(esk3_0))&~r1_tarski(esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 1.54/1.76  fof(c_0_17, plain, ![X28, X29]:(~v1_relat_1(X29)|r1_tarski(k10_relat_1(X29,X28),k1_relat_1(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 1.54/1.76  cnf(c_0_18, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.54/1.76  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.54/1.76  fof(c_0_20, plain, ![X17, X18]:(~r1_tarski(X17,X18)|k2_xboole_0(X17,X18)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.54/1.76  cnf(c_0_21, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.54/1.76  cnf(c_0_22, negated_conjecture, (v1_relat_1(k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.54/1.76  fof(c_0_23, plain, ![X33, X34]:(~v1_relat_1(X34)|(~r1_tarski(X33,k1_relat_1(X34))|k1_relat_1(k7_relat_1(X34,X33))=X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 1.54/1.76  fof(c_0_24, plain, ![X14, X15, X16]:(~r1_tarski(k2_xboole_0(X14,X15),X16)|r1_tarski(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 1.54/1.76  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.54/1.76  cnf(c_0_26, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),X2),k1_relat_1(k7_relat_1(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 1.54/1.76  fof(c_0_27, plain, ![X31, X32]:(~v1_relat_1(X32)|r1_tarski(k1_relat_1(k7_relat_1(X32,X31)),X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 1.54/1.76  cnf(c_0_28, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.54/1.76  cnf(c_0_29, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.54/1.76  cnf(c_0_30, negated_conjecture, (k2_xboole_0(k10_relat_1(k7_relat_1(esk3_0,X1),X2),k1_relat_1(k7_relat_1(esk3_0,X1)))=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.54/1.76  cnf(c_0_31, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.54/1.76  fof(c_0_32, plain, ![X26, X27]:(~v1_relat_1(X27)|k2_relat_1(k7_relat_1(X27,X26))=k9_relat_1(X27,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 1.54/1.76  cnf(c_0_33, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,X1))=X1|~r1_tarski(X1,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_19])).
% 1.54/1.76  cnf(c_0_34, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.54/1.76  fof(c_0_35, plain, ![X35, X36, X37]:(~v1_relat_1(X37)|k10_relat_1(k7_relat_1(X37,X35),X36)=k3_xboole_0(X35,k10_relat_1(X37,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 1.54/1.76  cnf(c_0_36, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),X2),X3)|~r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),X3)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.54/1.76  cnf(c_0_37, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),X1)), inference(spm,[status(thm)],[c_0_31, c_0_19])).
% 1.54/1.76  fof(c_0_38, plain, ![X30]:(~v1_relat_1(X30)|k10_relat_1(X30,k2_relat_1(X30))=k1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 1.54/1.76  cnf(c_0_39, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.54/1.76  fof(c_0_40, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k3_xboole_0(X19,X20)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 1.54/1.76  cnf(c_0_41, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.54/1.76  fof(c_0_42, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.54/1.76  cnf(c_0_43, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.54/1.76  cnf(c_0_44, negated_conjecture, (k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))=X2|~r1_tarski(X2,k1_relat_1(k7_relat_1(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_28, c_0_22])).
% 1.54/1.76  fof(c_0_45, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.54/1.76  cnf(c_0_46, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),X2),X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.54/1.76  cnf(c_0_47, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.54/1.76  cnf(c_0_48, negated_conjecture, (v1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))), inference(spm,[status(thm)],[c_0_18, c_0_22])).
% 1.54/1.76  cnf(c_0_49, negated_conjecture, (k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_39, c_0_22])).
% 1.54/1.76  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.54/1.76  cnf(c_0_51, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk3_0,esk2_0),X1),esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_41])).
% 1.54/1.76  cnf(c_0_52, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.54/1.76  cnf(c_0_53, negated_conjecture, (k3_xboole_0(X1,k10_relat_1(k7_relat_1(esk3_0,X2),X3))=k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,X2),X1),X3)), inference(spm,[status(thm)],[c_0_43, c_0_22])).
% 1.54/1.76  cnf(c_0_54, negated_conjecture, (k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),X1))=X1|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_44, c_0_41])).
% 1.54/1.76  cnf(c_0_55, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.54/1.76  cnf(c_0_56, negated_conjecture, (k2_xboole_0(k10_relat_1(k7_relat_1(esk3_0,X1),X2),X1)=X1), inference(spm,[status(thm)],[c_0_25, c_0_46])).
% 1.54/1.76  cnf(c_0_57, negated_conjecture, (k3_xboole_0(X1,k10_relat_1(esk3_0,X2))=k10_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_43, c_0_19])).
% 1.54/1.76  cnf(c_0_58, negated_conjecture, (k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),k9_relat_1(k7_relat_1(esk3_0,X1),X2))=k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 1.54/1.76  cnf(c_0_59, negated_conjecture, (k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),esk2_0),X1)=k10_relat_1(k7_relat_1(esk3_0,esk2_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])).
% 1.54/1.76  cnf(c_0_60, negated_conjecture, (k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_37]), c_0_41]), c_0_41])).
% 1.54/1.76  fof(c_0_61, plain, ![X21, X22, X23]:(~r1_tarski(X21,X22)|~r1_tarski(X23,X22)|r1_tarski(k2_xboole_0(X21,X23),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 1.54/1.76  cnf(c_0_62, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_55])).
% 1.54/1.76  cnf(c_0_63, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_29, c_0_56])).
% 1.54/1.76  cnf(c_0_64, negated_conjecture, (k3_xboole_0(k10_relat_1(esk3_0,X1),X2)=k10_relat_1(k7_relat_1(esk3_0,X2),X1)), inference(spm,[status(thm)],[c_0_52, c_0_57])).
% 1.54/1.76  cnf(c_0_65, negated_conjecture, (k10_relat_1(k7_relat_1(esk3_0,esk2_0),k9_relat_1(k7_relat_1(esk3_0,esk2_0),esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 1.54/1.76  cnf(c_0_66, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.54/1.76  cnf(c_0_67, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_29, c_0_62])).
% 1.54/1.76  cnf(c_0_68, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2)),X3),X1)), inference(spm,[status(thm)],[c_0_63, c_0_46])).
% 1.54/1.76  cnf(c_0_69, negated_conjecture, (k10_relat_1(k7_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2)),X3)=k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X3)),X2)), inference(spm,[status(thm)],[c_0_53, c_0_64])).
% 1.54/1.76  cnf(c_0_70, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2),X3),k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)))), inference(spm,[status(thm)],[c_0_21, c_0_48])).
% 1.54/1.76  cnf(c_0_71, negated_conjecture, (k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),X1),k9_relat_1(k7_relat_1(esk3_0,esk2_0),esk2_0))=k3_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_53, c_0_65])).
% 1.54/1.76  cnf(c_0_72, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 1.54/1.76  cnf(c_0_73, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)),X3),X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 1.54/1.76  cnf(c_0_74, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk2_0),k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),X1)))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 1.54/1.76  cnf(c_0_75, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,X1))=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_19])).
% 1.54/1.76  cnf(c_0_76, plain, (r1_tarski(k2_xboole_0(k2_xboole_0(X1,X2),X1),k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_72, c_0_62])).
% 1.54/1.76  cnf(c_0_77, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_50, c_0_67])).
% 1.54/1.76  cnf(c_0_78, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))),X1)), inference(spm,[status(thm)],[c_0_73, c_0_58])).
% 1.54/1.76  cnf(c_0_79, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk3_0,esk2_0),X1),k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),k10_relat_1(esk3_0,X1))))), inference(spm,[status(thm)],[c_0_74, c_0_64])).
% 1.54/1.76  cnf(c_0_80, negated_conjecture, (k10_relat_1(k7_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X1))=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_22]), c_0_75])).
% 1.54/1.76  cnf(c_0_81, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X1)=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_76]), c_0_52]), c_0_77])).
% 1.54/1.76  cnf(c_0_82, negated_conjecture, (k2_xboole_0(k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))),X1)=X1), inference(spm,[status(thm)],[c_0_25, c_0_78])).
% 1.54/1.76  cnf(c_0_83, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_41])).
% 1.54/1.76  cnf(c_0_84, negated_conjecture, (k2_xboole_0(X1,k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))))=X1), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 1.54/1.76  cnf(c_0_85, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)),X2)), inference(spm,[status(thm)],[c_0_31, c_0_22])).
% 1.54/1.76  cnf(c_0_86, negated_conjecture, (k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,esk2_0),k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_83]), c_0_84])).
% 1.54/1.76  cnf(c_0_87, negated_conjecture, (~r1_tarski(esk2_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.54/1.76  cnf(c_0_88, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87]), ['proof']).
% 1.54/1.76  # SZS output end CNFRefutation
% 1.54/1.76  # Proof object total steps             : 89
% 1.54/1.76  # Proof object clause steps            : 60
% 1.54/1.76  # Proof object formula steps           : 29
% 1.54/1.76  # Proof object conjectures             : 44
% 1.54/1.76  # Proof object clause conjectures      : 41
% 1.54/1.76  # Proof object formula conjectures     : 3
% 1.54/1.76  # Proof object initial clauses used    : 16
% 1.54/1.76  # Proof object initial formulas used   : 14
% 1.54/1.76  # Proof object generating inferences   : 43
% 1.54/1.76  # Proof object simplifying inferences  : 13
% 1.54/1.76  # Training examples: 0 positive, 0 negative
% 1.54/1.76  # Parsed axioms                        : 15
% 1.54/1.76  # Removed by relevancy pruning/SinE    : 0
% 1.54/1.76  # Initial clauses                      : 21
% 1.54/1.76  # Removed in clause preprocessing      : 0
% 1.54/1.76  # Initial clauses in saturation        : 21
% 1.54/1.76  # Processed clauses                    : 16892
% 1.54/1.76  # ...of these trivial                  : 1845
% 1.54/1.76  # ...subsumed                          : 13208
% 1.54/1.76  # ...remaining for further processing  : 1839
% 1.54/1.76  # Other redundant clauses eliminated   : 2
% 1.54/1.76  # Clauses deleted for lack of memory   : 0
% 1.54/1.76  # Backward-subsumed                    : 17
% 1.54/1.76  # Backward-rewritten                   : 164
% 1.54/1.76  # Generated clauses                    : 230147
% 1.54/1.76  # ...of the previous two non-trivial   : 148949
% 1.54/1.76  # Contextual simplify-reflections      : 0
% 1.54/1.76  # Paramodulations                      : 230145
% 1.54/1.76  # Factorizations                       : 0
% 1.54/1.76  # Equation resolutions                 : 2
% 1.54/1.76  # Propositional unsat checks           : 0
% 1.54/1.76  #    Propositional check models        : 0
% 1.54/1.76  #    Propositional check unsatisfiable : 0
% 1.54/1.76  #    Propositional clauses             : 0
% 1.54/1.76  #    Propositional clauses after purity: 0
% 1.54/1.76  #    Propositional unsat core size     : 0
% 1.54/1.76  #    Propositional preprocessing time  : 0.000
% 1.54/1.76  #    Propositional encoding time       : 0.000
% 1.54/1.76  #    Propositional solver time         : 0.000
% 1.54/1.76  #    Success case prop preproc time    : 0.000
% 1.54/1.76  #    Success case prop encoding time   : 0.000
% 1.54/1.76  #    Success case prop solver time     : 0.000
% 1.54/1.76  # Current number of processed clauses  : 1636
% 1.54/1.76  #    Positive orientable unit clauses  : 1069
% 1.54/1.76  #    Positive unorientable unit clauses: 4
% 1.54/1.76  #    Negative unit clauses             : 1
% 1.54/1.76  #    Non-unit-clauses                  : 562
% 1.54/1.76  # Current number of unprocessed clauses: 131300
% 1.54/1.76  # ...number of literals in the above   : 150580
% 1.54/1.76  # Current number of archived formulas  : 0
% 1.54/1.76  # Current number of archived clauses   : 201
% 1.54/1.76  # Clause-clause subsumption calls (NU) : 196765
% 1.54/1.76  # Rec. Clause-clause subsumption calls : 162510
% 1.54/1.76  # Non-unit clause-clause subsumptions  : 13167
% 1.54/1.76  # Unit Clause-clause subsumption calls : 3253
% 1.54/1.76  # Rewrite failures with RHS unbound    : 0
% 1.54/1.76  # BW rewrite match attempts            : 14441
% 1.54/1.76  # BW rewrite match successes           : 95
% 1.54/1.76  # Condensation attempts                : 0
% 1.54/1.76  # Condensation successes               : 0
% 1.54/1.76  # Termbank termtop insertions          : 4608798
% 1.54/1.77  
% 1.54/1.77  # -------------------------------------------------
% 1.54/1.77  # User time                : 1.337 s
% 1.54/1.77  # System time              : 0.072 s
% 1.54/1.77  # Total time               : 1.410 s
% 1.54/1.77  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
