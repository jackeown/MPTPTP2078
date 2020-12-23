%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:53 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 773 expanded)
%              Number of clauses        :   55 ( 345 expanded)
%              Number of leaves         :   16 ( 203 expanded)
%              Depth                    :   18
%              Number of atoms          :  180 (1217 expanded)
%              Number of equality atoms :   67 ( 714 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t109_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t147_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t174_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( X1 != k1_xboole_0
          & r1_tarski(X1,k2_relat_1(X2))
          & k10_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(c_0_16,plain,(
    ! [X22,X23] : k1_setfam_1(k2_tarski(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_17,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | r1_tarski(k4_xboole_0(X10,X12),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k1_setfam_1(k1_enumset1(X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_23])).

fof(c_0_28,plain,(
    ! [X15] : k4_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_29,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_27])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,k2_relat_1(X2))
         => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t147_funct_1])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X13,X14] : r1_tarski(k4_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_36,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_37,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r1_tarski(esk1_0,k2_relat_1(esk2_0))
    & k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

fof(c_0_38,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | k10_relat_1(X29,k6_subset_1(X27,X28)) = k6_subset_1(k10_relat_1(X29,X27),k10_relat_1(X29,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

fof(c_0_39,plain,(
    ! [X20,X21] : k6_subset_1(X20,X21) = k4_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_40,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_34]),c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk1_0,k2_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk2_0))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_48,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_49,plain,(
    ! [X24] :
      ( ~ v1_relat_1(X24)
      | k10_relat_1(X24,k2_relat_1(X24)) = k1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_50,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_45])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_31]),c_0_33])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk2_0))
    | ~ r1_tarski(X2,esk1_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_47])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_58,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | X25 = k1_xboole_0
      | ~ r1_tarski(X25,k2_relat_1(X26))
      | k10_relat_1(X26,X25) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t174_relat_1])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(esk2_0))
    | ~ r1_tarski(X1,k4_xboole_0(esk1_0,X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_41])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k1_relat_1(X1),k10_relat_1(X1,X2)) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_63,plain,
    ( X2 = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1))
    | k10_relat_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,X1),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_50])).

cnf(c_0_66,plain,
    ( r1_tarski(k10_relat_1(X1,k4_xboole_0(X2,X3)),k10_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_50])).

cnf(c_0_67,negated_conjecture,
    ( k10_relat_1(esk2_0,k2_relat_1(esk2_0)) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_33]),c_0_33]),c_0_56]),c_0_57])])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_69,negated_conjecture,
    ( k4_xboole_0(esk1_0,X1) = k1_xboole_0
    | k10_relat_1(esk2_0,k4_xboole_0(esk1_0,X1)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_57])])).

cnf(c_0_70,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,k2_relat_1(X1))) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_54])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k4_xboole_0(k2_relat_1(esk2_0),X1)),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_56]),c_0_57])])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_34]),c_0_33])).

fof(c_0_73,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r1_tarski(X32,k1_relat_1(X33))
      | r1_tarski(X32,k10_relat_1(X33,k9_relat_1(X33,X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_74,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | k10_relat_1(X1,k4_xboole_0(X2,X3)) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_50])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_relat_1(esk2_0)) = k1_xboole_0
    | ~ r1_tarski(k10_relat_1(esk2_0,esk1_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_56]),c_0_57])])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0))
    | ~ r1_tarski(X1,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_78,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | k10_relat_1(X1,k4_xboole_0(X2,k2_relat_1(X1))) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_54])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_relat_1(esk2_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_43])])).

cnf(c_0_80,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,k9_relat_1(X1,k10_relat_1(X1,X2)))) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,esk1_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_62]),c_0_56]),c_0_57])])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(esk1_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_80]),c_0_56]),c_0_57])]),c_0_81])])).

cnf(c_0_83,negated_conjecture,
    ( k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_84,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | r1_tarski(k9_relat_1(X31,k10_relat_1(X31,X30)),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)),esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_82]),c_0_33]),c_0_83])).

cnf(c_0_86,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_56]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.37/0.57  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.37/0.57  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.37/0.57  #
% 0.37/0.57  # Preprocessing time       : 0.045 s
% 0.37/0.57  # Presaturation interreduction done
% 0.37/0.57  
% 0.37/0.57  # Proof found!
% 0.37/0.57  # SZS status Theorem
% 0.37/0.57  # SZS output start CNFRefutation
% 0.37/0.57  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.37/0.57  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.37/0.57  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.37/0.57  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.37/0.57  fof(t109_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 0.37/0.57  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.37/0.57  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.37/0.57  fof(t147_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 0.37/0.57  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.37/0.57  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 0.37/0.57  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.37/0.57  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.37/0.57  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.37/0.57  fof(t174_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k2_relat_1(X2)))&k10_relat_1(X2,X1)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 0.37/0.57  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.37/0.57  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.37/0.57  fof(c_0_16, plain, ![X22, X23]:k1_setfam_1(k2_tarski(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.37/0.57  fof(c_0_17, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.37/0.57  fof(c_0_18, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.37/0.57  cnf(c_0_19, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.37/0.57  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.57  fof(c_0_21, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.37/0.57  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.57  cnf(c_0_23, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.37/0.57  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.37/0.57  fof(c_0_25, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|r1_tarski(k4_xboole_0(X10,X12),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).
% 0.37/0.57  cnf(c_0_26, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k1_setfam_1(k1_enumset1(X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_23])).
% 0.37/0.57  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[c_0_24, c_0_23])).
% 0.37/0.57  fof(c_0_28, plain, ![X15]:k4_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.37/0.57  fof(c_0_29, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.37/0.57  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.37/0.57  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_27])).
% 0.37/0.57  fof(c_0_32, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1))), inference(assume_negation,[status(cth)],[t147_funct_1])).
% 0.37/0.57  cnf(c_0_33, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.37/0.57  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.57  fof(c_0_35, plain, ![X13, X14]:r1_tarski(k4_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.37/0.57  cnf(c_0_36, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.37/0.57  fof(c_0_37, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(r1_tarski(esk1_0,k2_relat_1(esk2_0))&k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))!=esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 0.37/0.57  fof(c_0_38, plain, ![X27, X28, X29]:(~v1_relat_1(X29)|~v1_funct_1(X29)|k10_relat_1(X29,k6_subset_1(X27,X28))=k6_subset_1(k10_relat_1(X29,X27),k10_relat_1(X29,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 0.37/0.57  fof(c_0_39, plain, ![X20, X21]:k6_subset_1(X20,X21)=k4_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.37/0.57  cnf(c_0_40, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.37/0.57  cnf(c_0_41, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.37/0.57  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_34]), c_0_33])).
% 0.37/0.57  cnf(c_0_43, negated_conjecture, (r1_tarski(esk1_0,k2_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.37/0.57  cnf(c_0_44, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.37/0.57  cnf(c_0_45, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.37/0.57  cnf(c_0_46, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.37/0.57  cnf(c_0_47, negated_conjecture, (r1_tarski(X1,k2_relat_1(esk2_0))|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.37/0.57  fof(c_0_48, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.37/0.57  fof(c_0_49, plain, ![X24]:(~v1_relat_1(X24)|k10_relat_1(X24,k2_relat_1(X24))=k1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.37/0.57  cnf(c_0_50, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_45])).
% 0.37/0.57  cnf(c_0_51, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_31]), c_0_33])).
% 0.37/0.57  cnf(c_0_52, negated_conjecture, (r1_tarski(X1,k2_relat_1(esk2_0))|~r1_tarski(X2,esk1_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_42, c_0_47])).
% 0.37/0.57  cnf(c_0_53, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.37/0.57  cnf(c_0_54, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.37/0.57  cnf(c_0_55, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_51])).
% 0.37/0.57  cnf(c_0_56, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.37/0.57  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.37/0.57  fof(c_0_58, plain, ![X25, X26]:(~v1_relat_1(X26)|(X25=k1_xboole_0|~r1_tarski(X25,k2_relat_1(X26))|k10_relat_1(X26,X25)!=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t174_relat_1])])).
% 0.37/0.57  cnf(c_0_59, negated_conjecture, (r1_tarski(X1,k2_relat_1(esk2_0))|~r1_tarski(X1,k4_xboole_0(esk1_0,X2))), inference(spm,[status(thm)],[c_0_52, c_0_41])).
% 0.37/0.57  cnf(c_0_60, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_53])).
% 0.37/0.57  cnf(c_0_61, plain, (k4_xboole_0(k1_relat_1(X1),k10_relat_1(X1,X2))=k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),X2))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_54])).
% 0.37/0.57  cnf(c_0_62, negated_conjecture, (k10_relat_1(esk2_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.37/0.57  cnf(c_0_63, plain, (X2=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X2,k2_relat_1(X1))|k10_relat_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.37/0.57  cnf(c_0_64, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,X1),k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.37/0.57  cnf(c_0_65, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_34, c_0_50])).
% 0.37/0.57  cnf(c_0_66, plain, (r1_tarski(k10_relat_1(X1,k4_xboole_0(X2,X3)),k10_relat_1(X1,X2))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_50])).
% 0.37/0.57  cnf(c_0_67, negated_conjecture, (k10_relat_1(esk2_0,k2_relat_1(esk2_0))=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_33]), c_0_33]), c_0_56]), c_0_57])])).
% 0.37/0.57  cnf(c_0_68, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.57  cnf(c_0_69, negated_conjecture, (k4_xboole_0(esk1_0,X1)=k1_xboole_0|k10_relat_1(esk2_0,k4_xboole_0(esk1_0,X1))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_57])])).
% 0.37/0.57  cnf(c_0_70, plain, (k10_relat_1(X1,k4_xboole_0(X2,k2_relat_1(X1)))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_65, c_0_54])).
% 0.37/0.57  cnf(c_0_71, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k4_xboole_0(k2_relat_1(esk2_0),X1)),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_56]), c_0_57])])).
% 0.37/0.57  cnf(c_0_72, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_34]), c_0_33])).
% 0.37/0.57  fof(c_0_73, plain, ![X32, X33]:(~v1_relat_1(X33)|(~r1_tarski(X32,k1_relat_1(X33))|r1_tarski(X32,k10_relat_1(X33,k9_relat_1(X33,X32))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.37/0.57  cnf(c_0_74, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|k10_relat_1(X1,k4_xboole_0(X2,X3))!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_68, c_0_50])).
% 0.37/0.57  cnf(c_0_75, negated_conjecture, (k4_xboole_0(esk1_0,k2_relat_1(esk2_0))=k1_xboole_0|~r1_tarski(k10_relat_1(esk2_0,esk1_0),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_56]), c_0_57])])).
% 0.37/0.57  cnf(c_0_76, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0))|~r1_tarski(X1,k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.37/0.57  cnf(c_0_77, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.37/0.57  cnf(c_0_78, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|k10_relat_1(X1,k4_xboole_0(X2,k2_relat_1(X1)))!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_74, c_0_54])).
% 0.37/0.57  cnf(c_0_79, negated_conjecture, (k4_xboole_0(esk1_0,k2_relat_1(esk2_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_43])])).
% 0.37/0.57  cnf(c_0_80, plain, (k10_relat_1(X1,k4_xboole_0(X2,k9_relat_1(X1,k10_relat_1(X1,X2))))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_65, c_0_77])).
% 0.37/0.57  cnf(c_0_81, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,esk1_0),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_62]), c_0_56]), c_0_57])])).
% 0.37/0.57  cnf(c_0_82, negated_conjecture, (k4_xboole_0(esk1_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_80]), c_0_56]), c_0_57])]), c_0_81])])).
% 0.37/0.57  cnf(c_0_83, negated_conjecture, (k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.37/0.57  fof(c_0_84, plain, ![X30, X31]:(~v1_relat_1(X31)|~v1_funct_1(X31)|r1_tarski(k9_relat_1(X31,k10_relat_1(X31,X30)),X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.37/0.57  cnf(c_0_85, negated_conjecture, (~r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)),esk1_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_82]), c_0_33]), c_0_83])).
% 0.37/0.57  cnf(c_0_86, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.37/0.57  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_56]), c_0_57])]), ['proof']).
% 0.37/0.57  # SZS output end CNFRefutation
% 0.37/0.57  # Proof object total steps             : 88
% 0.37/0.57  # Proof object clause steps            : 55
% 0.37/0.57  # Proof object formula steps           : 33
% 0.37/0.57  # Proof object conjectures             : 22
% 0.37/0.57  # Proof object clause conjectures      : 19
% 0.37/0.57  # Proof object formula conjectures     : 3
% 0.37/0.57  # Proof object initial clauses used    : 20
% 0.37/0.57  # Proof object initial formulas used   : 16
% 0.37/0.57  # Proof object generating inferences   : 29
% 0.37/0.57  # Proof object simplifying inferences  : 44
% 0.37/0.57  # Training examples: 0 positive, 0 negative
% 0.37/0.57  # Parsed axioms                        : 16
% 0.37/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.57  # Initial clauses                      : 22
% 0.37/0.57  # Removed in clause preprocessing      : 3
% 0.37/0.57  # Initial clauses in saturation        : 19
% 0.37/0.57  # Processed clauses                    : 2601
% 0.37/0.57  # ...of these trivial                  : 77
% 0.37/0.57  # ...subsumed                          : 2031
% 0.37/0.57  # ...remaining for further processing  : 493
% 0.37/0.57  # Other redundant clauses eliminated   : 28
% 0.37/0.57  # Clauses deleted for lack of memory   : 0
% 0.37/0.57  # Backward-subsumed                    : 63
% 0.37/0.57  # Backward-rewritten                   : 32
% 0.37/0.57  # Generated clauses                    : 12296
% 0.37/0.57  # ...of the previous two non-trivial   : 9945
% 0.37/0.57  # Contextual simplify-reflections      : 15
% 0.37/0.57  # Paramodulations                      : 12268
% 0.37/0.57  # Factorizations                       : 0
% 0.37/0.57  # Equation resolutions                 : 28
% 0.37/0.57  # Propositional unsat checks           : 0
% 0.37/0.57  #    Propositional check models        : 0
% 0.37/0.57  #    Propositional check unsatisfiable : 0
% 0.37/0.57  #    Propositional clauses             : 0
% 0.37/0.57  #    Propositional clauses after purity: 0
% 0.37/0.57  #    Propositional unsat core size     : 0
% 0.37/0.57  #    Propositional preprocessing time  : 0.000
% 0.37/0.57  #    Propositional encoding time       : 0.000
% 0.37/0.57  #    Propositional solver time         : 0.000
% 0.37/0.57  #    Success case prop preproc time    : 0.000
% 0.37/0.57  #    Success case prop encoding time   : 0.000
% 0.37/0.57  #    Success case prop solver time     : 0.000
% 0.37/0.57  # Current number of processed clauses  : 378
% 0.37/0.57  #    Positive orientable unit clauses  : 23
% 0.37/0.57  #    Positive unorientable unit clauses: 1
% 0.37/0.57  #    Negative unit clauses             : 2
% 0.37/0.57  #    Non-unit-clauses                  : 352
% 0.37/0.57  # Current number of unprocessed clauses: 7179
% 0.37/0.57  # ...number of literals in the above   : 28896
% 0.37/0.57  # Current number of archived formulas  : 0
% 0.37/0.57  # Current number of archived clauses   : 116
% 0.37/0.57  # Clause-clause subsumption calls (NU) : 22640
% 0.37/0.57  # Rec. Clause-clause subsumption calls : 16956
% 0.37/0.57  # Non-unit clause-clause subsumptions  : 2107
% 0.37/0.57  # Unit Clause-clause subsumption calls : 13
% 0.37/0.57  # Rewrite failures with RHS unbound    : 0
% 0.37/0.57  # BW rewrite match attempts            : 23
% 0.37/0.57  # BW rewrite match successes           : 13
% 0.37/0.57  # Condensation attempts                : 0
% 0.37/0.57  # Condensation successes               : 0
% 0.37/0.57  # Termbank termtop insertions          : 154812
% 0.37/0.57  
% 0.37/0.57  # -------------------------------------------------
% 0.37/0.57  # User time                : 0.222 s
% 0.37/0.57  # System time              : 0.009 s
% 0.37/0.57  # Total time               : 0.231 s
% 0.37/0.57  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
