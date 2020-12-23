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
% DateTime   : Thu Dec  3 10:54:53 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 410 expanded)
%              Number of clauses        :   45 ( 175 expanded)
%              Number of leaves         :   14 ( 106 expanded)
%              Depth                    :    9
%              Number of atoms          :  145 ( 833 expanded)
%              Number of equality atoms :   54 ( 349 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t147_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(t174_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( X1 != k1_xboole_0
          & r1_tarski(X1,k2_relat_1(X2))
          & k10_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

fof(c_0_14,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_15,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_16,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k3_xboole_0(X11,X12) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,k2_relat_1(X2))
         => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t147_funct_1])).

fof(c_0_18,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_19,plain,(
    ! [X25,X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ v1_funct_1(X27)
      | k10_relat_1(X27,k6_subset_1(X25,X26)) = k6_subset_1(k10_relat_1(X27,X25),k10_relat_1(X27,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

fof(c_0_20,plain,(
    ! [X19,X20] : k6_subset_1(X19,X20) = k4_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_21,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,k4_xboole_0(X16,X15))
      | X15 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X13,X14] : r1_tarski(k4_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_26,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | r1_tarski(k9_relat_1(X29,k10_relat_1(X29,X28)),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_27,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r1_tarski(esk1_0,k2_relat_1(esk2_0))
    & k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_29,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | r1_tarski(k10_relat_1(X22,X21),k1_relat_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_30,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_31,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_36,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_28])).

fof(c_0_41,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ r1_tarski(X30,k1_relat_1(X31))
      | r1_tarski(X30,k10_relat_1(X31,k9_relat_1(X31,X30))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk1_0,k2_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_45,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_32])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_40])).

cnf(c_0_50,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_39])).

fof(c_0_52,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | X23 = k1_xboole_0
      | ~ r1_tarski(X23,k2_relat_1(X24))
      | k10_relat_1(X24,X23) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t174_relat_1])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk2_0))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,X2)) = k10_relat_1(esk2_0,k4_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_38]),c_0_39])])).

cnf(c_0_55,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_36])])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)))) = k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_48]),c_0_34])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_49]),c_0_36])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_39])])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_60,plain,
    ( X2 = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1))
    | k10_relat_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,X1),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_36])).

cnf(c_0_62,negated_conjecture,
    ( k10_relat_1(esk2_0,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(k10_relat_1(esk2_0,k4_xboole_0(X1,X2)),k10_relat_1(esk2_0,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_54]),c_0_54]),c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_49,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1))) = k10_relat_1(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_58]),c_0_54]),c_0_54]),c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k4_xboole_0(X1,X2)),k10_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_54])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_36])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(esk1_0,X1) = k1_xboole_0
    | k10_relat_1(esk2_0,k4_xboole_0(esk1_0,X1)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_39])])).

cnf(c_0_69,negated_conjecture,
    ( k10_relat_1(esk2_0,k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_65]),c_0_66])])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | ~ r1_tarski(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_34])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(esk1_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_64]),c_0_64]),c_0_48])]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:14:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.45  # AutoSched0-Mode selected heuristic G_E___208_C09_12_F1_SE_CS_SP_PS_S064A
% 0.21/0.45  # and selection function SelectComplexG.
% 0.21/0.45  #
% 0.21/0.45  # Preprocessing time       : 0.027 s
% 0.21/0.45  # Presaturation interreduction done
% 0.21/0.45  
% 0.21/0.45  # Proof found!
% 0.21/0.45  # SZS status Theorem
% 0.21/0.45  # SZS output start CNFRefutation
% 0.21/0.45  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.45  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.45  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.45  fof(t147_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 0.21/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.45  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 0.21/0.45  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.21/0.45  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 0.21/0.45  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.21/0.45  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.21/0.45  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.21/0.45  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.21/0.45  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 0.21/0.45  fof(t174_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k2_relat_1(X2)))&k10_relat_1(X2,X1)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 0.21/0.45  fof(c_0_14, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.45  fof(c_0_15, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.45  fof(c_0_16, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k3_xboole_0(X11,X12)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.45  fof(c_0_17, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1))), inference(assume_negation,[status(cth)],[t147_funct_1])).
% 0.21/0.45  fof(c_0_18, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.45  fof(c_0_19, plain, ![X25, X26, X27]:(~v1_relat_1(X27)|~v1_funct_1(X27)|k10_relat_1(X27,k6_subset_1(X25,X26))=k6_subset_1(k10_relat_1(X27,X25),k10_relat_1(X27,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 0.21/0.45  fof(c_0_20, plain, ![X19, X20]:k6_subset_1(X19,X20)=k4_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.21/0.45  fof(c_0_21, plain, ![X15, X16]:(~r1_tarski(X15,k4_xboole_0(X16,X15))|X15=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 0.21/0.45  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.45  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.45  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.45  fof(c_0_25, plain, ![X13, X14]:r1_tarski(k4_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.21/0.45  fof(c_0_26, plain, ![X28, X29]:(~v1_relat_1(X29)|~v1_funct_1(X29)|r1_tarski(k9_relat_1(X29,k10_relat_1(X29,X28)),X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.21/0.45  fof(c_0_27, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(r1_tarski(esk1_0,k2_relat_1(esk2_0))&k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))!=esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.21/0.45  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.45  fof(c_0_29, plain, ![X21, X22]:(~v1_relat_1(X22)|r1_tarski(k10_relat_1(X22,X21),k1_relat_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.21/0.45  fof(c_0_30, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X9,X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.21/0.45  cnf(c_0_31, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.45  cnf(c_0_32, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.45  cnf(c_0_33, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.45  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_23])).
% 0.21/0.45  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_23])).
% 0.21/0.45  cnf(c_0_36, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.45  cnf(c_0_37, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.45  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.45  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.45  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_28])).
% 0.21/0.45  fof(c_0_41, plain, ![X30, X31]:(~v1_relat_1(X31)|(~r1_tarski(X30,k1_relat_1(X31))|r1_tarski(X30,k10_relat_1(X31,k9_relat_1(X31,X30))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.21/0.45  cnf(c_0_42, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.45  cnf(c_0_43, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.45  cnf(c_0_44, negated_conjecture, (r1_tarski(esk1_0,k2_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.45  cnf(c_0_45, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_32])).
% 0.21/0.45  cnf(c_0_46, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.45  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_34])).
% 0.21/0.45  cnf(c_0_48, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.21/0.45  cnf(c_0_49, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(spm,[status(thm)],[c_0_35, c_0_40])).
% 0.21/0.45  cnf(c_0_50, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.45  cnf(c_0_51, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_42, c_0_39])).
% 0.21/0.45  fof(c_0_52, plain, ![X23, X24]:(~v1_relat_1(X24)|(X23=k1_xboole_0|~r1_tarski(X23,k2_relat_1(X24))|k10_relat_1(X24,X23)!=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t174_relat_1])])).
% 0.21/0.45  cnf(c_0_53, negated_conjecture, (r1_tarski(X1,k2_relat_1(esk2_0))|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.45  cnf(c_0_54, negated_conjecture, (k4_xboole_0(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,X2))=k10_relat_1(esk2_0,k4_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_38]), c_0_39])])).
% 0.21/0.45  cnf(c_0_55, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_36])])).
% 0.21/0.45  cnf(c_0_56, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1))))=k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_48]), c_0_34])).
% 0.21/0.45  cnf(c_0_57, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_49]), c_0_36])])).
% 0.21/0.45  cnf(c_0_58, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_39])])).
% 0.21/0.45  cnf(c_0_59, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.45  cnf(c_0_60, plain, (X2=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X2,k2_relat_1(X1))|k10_relat_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.45  cnf(c_0_61, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,X1),k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_53, c_0_36])).
% 0.21/0.45  cnf(c_0_62, negated_conjecture, (k10_relat_1(esk2_0,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(k10_relat_1(esk2_0,k4_xboole_0(X1,X2)),k10_relat_1(esk2_0,k4_xboole_0(X2,k4_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_54]), c_0_54]), c_0_54])).
% 0.21/0.45  cnf(c_0_63, negated_conjecture, (k4_xboole_0(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.21/0.45  cnf(c_0_64, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_49, c_0_57])).
% 0.21/0.45  cnf(c_0_65, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)))=k10_relat_1(esk2_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_58]), c_0_54]), c_0_54]), c_0_56])).
% 0.21/0.45  cnf(c_0_66, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k4_xboole_0(X1,X2)),k10_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_36, c_0_54])).
% 0.21/0.45  cnf(c_0_67, plain, (k4_xboole_0(X1,X2)=X1|~r1_tarski(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_59, c_0_36])).
% 0.21/0.45  cnf(c_0_68, negated_conjecture, (k4_xboole_0(esk1_0,X1)=k1_xboole_0|k10_relat_1(esk2_0,k4_xboole_0(esk1_0,X1))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_39])])).
% 0.21/0.45  cnf(c_0_69, negated_conjecture, (k10_relat_1(esk2_0,k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1))))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_65]), c_0_66])])).
% 0.21/0.45  cnf(c_0_70, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|~r1_tarski(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_67, c_0_34])).
% 0.21/0.45  cnf(c_0_71, negated_conjecture, (k4_xboole_0(esk1_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.21/0.45  cnf(c_0_72, negated_conjecture, (k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.45  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_64]), c_0_64]), c_0_48])]), c_0_72]), ['proof']).
% 0.21/0.45  # SZS output end CNFRefutation
% 0.21/0.45  # Proof object total steps             : 74
% 0.21/0.45  # Proof object clause steps            : 45
% 0.21/0.45  # Proof object formula steps           : 29
% 0.21/0.45  # Proof object conjectures             : 22
% 0.21/0.45  # Proof object clause conjectures      : 19
% 0.21/0.45  # Proof object formula conjectures     : 3
% 0.21/0.45  # Proof object initial clauses used    : 18
% 0.21/0.45  # Proof object initial formulas used   : 14
% 0.21/0.45  # Proof object generating inferences   : 22
% 0.21/0.45  # Proof object simplifying inferences  : 35
% 0.21/0.45  # Training examples: 0 positive, 0 negative
% 0.21/0.45  # Parsed axioms                        : 14
% 0.21/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.45  # Initial clauses                      : 19
% 0.21/0.45  # Removed in clause preprocessing      : 2
% 0.21/0.45  # Initial clauses in saturation        : 17
% 0.21/0.45  # Processed clauses                    : 1281
% 0.21/0.45  # ...of these trivial                  : 70
% 0.21/0.45  # ...subsumed                          : 908
% 0.21/0.45  # ...remaining for further processing  : 303
% 0.21/0.45  # Other redundant clauses eliminated   : 2
% 0.21/0.45  # Clauses deleted for lack of memory   : 0
% 0.21/0.45  # Backward-subsumed                    : 4
% 0.21/0.45  # Backward-rewritten                   : 72
% 0.21/0.45  # Generated clauses                    : 5024
% 0.21/0.45  # ...of the previous two non-trivial   : 3111
% 0.21/0.45  # Contextual simplify-reflections      : 0
% 0.21/0.45  # Paramodulations                      : 5022
% 0.21/0.45  # Factorizations                       : 0
% 0.21/0.45  # Equation resolutions                 : 2
% 0.21/0.45  # Propositional unsat checks           : 0
% 0.21/0.45  #    Propositional check models        : 0
% 0.21/0.45  #    Propositional check unsatisfiable : 0
% 0.21/0.45  #    Propositional clauses             : 0
% 0.21/0.45  #    Propositional clauses after purity: 0
% 0.21/0.45  #    Propositional unsat core size     : 0
% 0.21/0.45  #    Propositional preprocessing time  : 0.000
% 0.21/0.45  #    Propositional encoding time       : 0.000
% 0.21/0.45  #    Propositional solver time         : 0.000
% 0.21/0.45  #    Success case prop preproc time    : 0.000
% 0.21/0.45  #    Success case prop encoding time   : 0.000
% 0.21/0.45  #    Success case prop solver time     : 0.000
% 0.21/0.45  # Current number of processed clauses  : 209
% 0.21/0.45  #    Positive orientable unit clauses  : 101
% 0.21/0.45  #    Positive unorientable unit clauses: 1
% 0.21/0.45  #    Negative unit clauses             : 1
% 0.21/0.45  #    Non-unit-clauses                  : 106
% 0.21/0.45  # Current number of unprocessed clauses: 1704
% 0.21/0.45  # ...number of literals in the above   : 2422
% 0.21/0.45  # Current number of archived formulas  : 0
% 0.21/0.45  # Current number of archived clauses   : 94
% 0.21/0.45  # Clause-clause subsumption calls (NU) : 6700
% 0.21/0.45  # Rec. Clause-clause subsumption calls : 5430
% 0.21/0.45  # Non-unit clause-clause subsumptions  : 909
% 0.21/0.45  # Unit Clause-clause subsumption calls : 23
% 0.21/0.45  # Rewrite failures with RHS unbound    : 0
% 0.21/0.45  # BW rewrite match attempts            : 322
% 0.21/0.45  # BW rewrite match successes           : 32
% 0.21/0.45  # Condensation attempts                : 0
% 0.21/0.45  # Condensation successes               : 0
% 0.21/0.45  # Termbank termtop insertions          : 73396
% 0.21/0.45  
% 0.21/0.45  # -------------------------------------------------
% 0.21/0.45  # User time                : 0.093 s
% 0.21/0.45  # System time              : 0.009 s
% 0.21/0.45  # Total time               : 0.103 s
% 0.21/0.45  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
