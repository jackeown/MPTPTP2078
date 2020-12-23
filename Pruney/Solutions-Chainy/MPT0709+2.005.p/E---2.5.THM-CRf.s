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
% DateTime   : Thu Dec  3 10:55:31 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 319 expanded)
%              Number of clauses        :   46 ( 131 expanded)
%              Number of leaves         :   16 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :  172 ( 751 expanded)
%              Number of equality atoms :   55 ( 263 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t123_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t164_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( r1_tarski(X1,k1_relat_1(X2))
          & v2_funct_1(X2) )
       => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t148_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t170_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

fof(t157_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))
          & r1_tarski(X1,k1_relat_1(X3))
          & v2_funct_1(X3) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(c_0_16,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),X6) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_17,plain,(
    ! [X16,X17] : k1_setfam_1(k2_tarski(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,plain,(
    ! [X9] :
      ( ~ r1_tarski(X9,k1_xboole_0)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_23,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k2_tarski(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_24,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_25,plain,(
    ! [X23,X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | ~ v2_funct_1(X25)
      | k9_relat_1(X25,k6_subset_1(X23,X24)) = k6_subset_1(k9_relat_1(X25,X23),k9_relat_1(X25,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).

fof(c_0_26,plain,(
    ! [X14,X15] : k6_subset_1(X14,X15) = k4_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X8] : k4_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_31,plain,
    ( k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( r1_tarski(X1,k1_relat_1(X2))
            & v2_funct_1(X2) )
         => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_1])).

fof(c_0_37,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_38,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | r1_tarski(k10_relat_1(X20,X19),k1_relat_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_39,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | k9_relat_1(X29,k10_relat_1(X29,X28)) = k3_xboole_0(X28,k9_relat_1(X29,k1_relat_1(X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).

fof(c_0_40,plain,(
    ! [X18] :
      ( ~ v1_relat_1(X18)
      | k9_relat_1(X18,k1_relat_1(X18)) = k2_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_41,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_32])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

fof(c_0_43,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & v2_funct_1(esk2_0)
    & k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_44,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_46,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ r1_tarski(X26,k1_relat_1(X27))
      | r1_tarski(X26,k10_relat_1(X27,k9_relat_1(X27,X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( k10_relat_1(X1,X2) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k1_setfam_1(k2_tarski(X2,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_48,c_0_20])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k2_relat_1(X1),k9_relat_1(X1,X2)) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X2))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( k9_relat_1(esk2_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])])).

fof(c_0_60,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | r1_tarski(k10_relat_1(X22,X21),k10_relat_1(X22,k2_relat_1(X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).

cnf(c_0_61,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1))) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_62,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_relat_1(X2))) = k9_relat_1(X2,k10_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( k2_relat_1(esk2_0) = k9_relat_1(esk2_0,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_35]),c_0_35]),c_0_51]),c_0_52]),c_0_53])])).

cnf(c_0_64,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_49])).

fof(c_0_66,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ v1_funct_1(X32)
      | ~ r1_tarski(k9_relat_1(X32,X30),k9_relat_1(X32,X31))
      | ~ r1_tarski(X30,k1_relat_1(X32))
      | ~ v2_funct_1(X32)
      | r1_tarski(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_funct_1])])).

cnf(c_0_67,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,k9_relat_1(esk2_0,k1_relat_1(esk2_0)))) = k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_52]),c_0_53])])).

cnf(c_0_68,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_49])).

cnf(c_0_69,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0))) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_63]),c_0_53])])).

cnf(c_0_70,plain,
    ( r1_tarski(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_53])])).

cnf(c_0_73,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_55])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_51]),c_0_52]),c_0_53]),c_0_72])])).

cnf(c_0_75,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_76,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)) = X1
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_53])])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.26  % Computer   : n016.cluster.edu
% 0.08/0.26  % Model      : x86_64 x86_64
% 0.08/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.26  % Memory     : 8042.1875MB
% 0.08/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.26  % CPULimit   : 60
% 0.08/0.26  % WCLimit    : 600
% 0.08/0.26  % DateTime   : Tue Dec  1 11:06:04 EST 2020
% 0.11/0.26  % CPUTime    : 
% 0.11/0.26  # Version: 2.5pre002
% 0.11/0.26  # No SInE strategy applied
% 0.11/0.26  # Trying AutoSched0 for 299 seconds
% 0.11/0.28  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.11/0.28  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.11/0.28  #
% 0.11/0.28  # Preprocessing time       : 0.014 s
% 0.11/0.28  # Presaturation interreduction done
% 0.11/0.28  
% 0.11/0.28  # Proof found!
% 0.11/0.28  # SZS status Theorem
% 0.11/0.28  # SZS output start CNFRefutation
% 0.11/0.28  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.11/0.28  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.11/0.28  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.11/0.28  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.11/0.28  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.11/0.28  fof(t123_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 0.11/0.28  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.11/0.28  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.11/0.28  fof(t164_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 0.11/0.28  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.11/0.28  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 0.11/0.28  fof(t148_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 0.11/0.28  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.11/0.28  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.11/0.28  fof(t170_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 0.11/0.28  fof(t157_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))&r1_tarski(X1,k1_relat_1(X3)))&v2_funct_1(X3))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 0.11/0.28  fof(c_0_16, plain, ![X6, X7]:r1_tarski(k3_xboole_0(X6,X7),X6), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.11/0.28  fof(c_0_17, plain, ![X16, X17]:k1_setfam_1(k2_tarski(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.11/0.28  fof(c_0_18, plain, ![X9]:(~r1_tarski(X9,k1_xboole_0)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.11/0.28  cnf(c_0_19, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.11/0.28  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.11/0.28  cnf(c_0_21, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.11/0.28  cnf(c_0_22, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.11/0.28  fof(c_0_23, plain, ![X12, X13]:k2_tarski(X12,X13)=k2_tarski(X13,X12), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.11/0.28  fof(c_0_24, plain, ![X10, X11]:k4_xboole_0(X10,k4_xboole_0(X10,X11))=k3_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.11/0.28  fof(c_0_25, plain, ![X23, X24, X25]:(~v1_relat_1(X25)|~v1_funct_1(X25)|(~v2_funct_1(X25)|k9_relat_1(X25,k6_subset_1(X23,X24))=k6_subset_1(k9_relat_1(X25,X23),k9_relat_1(X25,X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).
% 0.11/0.28  fof(c_0_26, plain, ![X14, X15]:k6_subset_1(X14,X15)=k4_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.11/0.28  cnf(c_0_27, plain, (k1_setfam_1(k2_tarski(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.11/0.28  cnf(c_0_28, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.11/0.28  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.11/0.28  fof(c_0_30, plain, ![X8]:k4_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.11/0.28  cnf(c_0_31, plain, (k9_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.11/0.28  cnf(c_0_32, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.11/0.28  cnf(c_0_33, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.11/0.28  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_29, c_0_20])).
% 0.11/0.28  cnf(c_0_35, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.11/0.28  fof(c_0_36, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1))), inference(assume_negation,[status(cth)],[t164_funct_1])).
% 0.11/0.28  fof(c_0_37, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.11/0.28  fof(c_0_38, plain, ![X19, X20]:(~v1_relat_1(X20)|r1_tarski(k10_relat_1(X20,X19),k1_relat_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.11/0.28  fof(c_0_39, plain, ![X28, X29]:(~v1_relat_1(X29)|~v1_funct_1(X29)|k9_relat_1(X29,k10_relat_1(X29,X28))=k3_xboole_0(X28,k9_relat_1(X29,k1_relat_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).
% 0.11/0.28  fof(c_0_40, plain, ![X18]:(~v1_relat_1(X18)|k9_relat_1(X18,k1_relat_1(X18))=k2_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.11/0.28  cnf(c_0_41, plain, (k9_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_32])).
% 0.11/0.28  cnf(c_0_42, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.11/0.28  fof(c_0_43, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((r1_tarski(esk1_0,k1_relat_1(esk2_0))&v2_funct_1(esk2_0))&k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))!=esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 0.11/0.28  cnf(c_0_44, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.11/0.28  cnf(c_0_45, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.11/0.28  fof(c_0_46, plain, ![X26, X27]:(~v1_relat_1(X27)|(~r1_tarski(X26,k1_relat_1(X27))|r1_tarski(X26,k10_relat_1(X27,k9_relat_1(X27,X26))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.11/0.28  cnf(c_0_47, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.11/0.28  cnf(c_0_48, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.11/0.28  cnf(c_0_49, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.11/0.28  cnf(c_0_50, plain, (k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_42])).
% 0.11/0.28  cnf(c_0_51, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.11/0.28  cnf(c_0_52, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.11/0.28  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.11/0.28  cnf(c_0_54, plain, (k10_relat_1(X1,X2)=k1_relat_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.11/0.28  cnf(c_0_55, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.11/0.28  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_47])).
% 0.11/0.28  cnf(c_0_57, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k1_setfam_1(k2_tarski(X2,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[c_0_48, c_0_20])).
% 0.11/0.28  cnf(c_0_58, plain, (k4_xboole_0(k2_relat_1(X1),k9_relat_1(X1,X2))=k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X2))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_49])).
% 0.11/0.28  cnf(c_0_59, negated_conjecture, (k9_relat_1(esk2_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])])).
% 0.11/0.28  fof(c_0_60, plain, ![X21, X22]:(~v1_relat_1(X22)|r1_tarski(k10_relat_1(X22,X21),k10_relat_1(X22,k2_relat_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).
% 0.11/0.28  cnf(c_0_61, plain, (k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1)))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.11/0.28  cnf(c_0_62, plain, (k1_setfam_1(k2_tarski(X1,k2_relat_1(X2)))=k9_relat_1(X2,k10_relat_1(X2,X1))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_57, c_0_49])).
% 0.11/0.28  cnf(c_0_63, negated_conjecture, (k2_relat_1(esk2_0)=k9_relat_1(esk2_0,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_35]), c_0_35]), c_0_51]), c_0_52]), c_0_53])])).
% 0.11/0.28  cnf(c_0_64, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.11/0.28  cnf(c_0_65, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_61, c_0_49])).
% 0.11/0.28  fof(c_0_66, plain, ![X30, X31, X32]:(~v1_relat_1(X32)|~v1_funct_1(X32)|(~r1_tarski(k9_relat_1(X32,X30),k9_relat_1(X32,X31))|~r1_tarski(X30,k1_relat_1(X32))|~v2_funct_1(X32)|r1_tarski(X30,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_funct_1])])).
% 0.11/0.28  cnf(c_0_67, negated_conjecture, (k1_setfam_1(k2_tarski(X1,k9_relat_1(esk2_0,k1_relat_1(esk2_0))))=k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_52]), c_0_53])])).
% 0.11/0.28  cnf(c_0_68, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_64, c_0_49])).
% 0.11/0.28  cnf(c_0_69, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(esk2_0,k1_relat_1(esk2_0)))=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_63]), c_0_53])])).
% 0.11/0.28  cnf(c_0_70, plain, (r1_tarski(X2,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~r1_tarski(X2,k1_relat_1(X1))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.11/0.28  cnf(c_0_71, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1)), inference(spm,[status(thm)],[c_0_22, c_0_67])).
% 0.11/0.28  cnf(c_0_72, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_53])])).
% 0.11/0.28  cnf(c_0_73, plain, (k10_relat_1(X1,k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)|~r1_tarski(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_55])).
% 0.11/0.28  cnf(c_0_74, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_51]), c_0_52]), c_0_53]), c_0_72])])).
% 0.11/0.28  cnf(c_0_75, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.11/0.28  cnf(c_0_76, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1))=X1|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_53])])).
% 0.11/0.28  cnf(c_0_77, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.11/0.28  cnf(c_0_78, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])]), ['proof']).
% 0.11/0.28  # SZS output end CNFRefutation
% 0.11/0.28  # Proof object total steps             : 79
% 0.11/0.28  # Proof object clause steps            : 46
% 0.11/0.28  # Proof object formula steps           : 33
% 0.11/0.28  # Proof object conjectures             : 17
% 0.11/0.28  # Proof object clause conjectures      : 14
% 0.11/0.28  # Proof object formula conjectures     : 3
% 0.11/0.28  # Proof object initial clauses used    : 21
% 0.11/0.28  # Proof object initial formulas used   : 16
% 0.11/0.28  # Proof object generating inferences   : 20
% 0.11/0.28  # Proof object simplifying inferences  : 35
% 0.11/0.28  # Training examples: 0 positive, 0 negative
% 0.11/0.28  # Parsed axioms                        : 16
% 0.11/0.28  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.28  # Initial clauses                      : 22
% 0.11/0.28  # Removed in clause preprocessing      : 2
% 0.11/0.28  # Initial clauses in saturation        : 20
% 0.11/0.28  # Processed clauses                    : 253
% 0.11/0.28  # ...of these trivial                  : 12
% 0.11/0.28  # ...subsumed                          : 113
% 0.11/0.28  # ...remaining for further processing  : 128
% 0.11/0.28  # Other redundant clauses eliminated   : 2
% 0.11/0.28  # Clauses deleted for lack of memory   : 0
% 0.11/0.28  # Backward-subsumed                    : 3
% 0.11/0.28  # Backward-rewritten                   : 18
% 0.11/0.28  # Generated clauses                    : 650
% 0.11/0.28  # ...of the previous two non-trivial   : 484
% 0.11/0.28  # Contextual simplify-reflections      : 1
% 0.11/0.28  # Paramodulations                      : 648
% 0.11/0.28  # Factorizations                       : 0
% 0.11/0.28  # Equation resolutions                 : 2
% 0.11/0.28  # Propositional unsat checks           : 0
% 0.11/0.28  #    Propositional check models        : 0
% 0.11/0.28  #    Propositional check unsatisfiable : 0
% 0.11/0.28  #    Propositional clauses             : 0
% 0.11/0.28  #    Propositional clauses after purity: 0
% 0.11/0.28  #    Propositional unsat core size     : 0
% 0.11/0.28  #    Propositional preprocessing time  : 0.000
% 0.11/0.28  #    Propositional encoding time       : 0.000
% 0.11/0.28  #    Propositional solver time         : 0.000
% 0.11/0.28  #    Success case prop preproc time    : 0.000
% 0.11/0.28  #    Success case prop encoding time   : 0.000
% 0.11/0.28  #    Success case prop solver time     : 0.000
% 0.11/0.28  # Current number of processed clauses  : 86
% 0.11/0.28  #    Positive orientable unit clauses  : 27
% 0.11/0.28  #    Positive unorientable unit clauses: 3
% 0.11/0.28  #    Negative unit clauses             : 1
% 0.11/0.28  #    Non-unit-clauses                  : 55
% 0.11/0.28  # Current number of unprocessed clauses: 253
% 0.11/0.28  # ...number of literals in the above   : 818
% 0.11/0.28  # Current number of archived formulas  : 0
% 0.11/0.28  # Current number of archived clauses   : 42
% 0.11/0.28  # Clause-clause subsumption calls (NU) : 765
% 0.11/0.28  # Rec. Clause-clause subsumption calls : 620
% 0.11/0.28  # Non-unit clause-clause subsumptions  : 113
% 0.11/0.28  # Unit Clause-clause subsumption calls : 11
% 0.11/0.28  # Rewrite failures with RHS unbound    : 0
% 0.11/0.28  # BW rewrite match attempts            : 39
% 0.11/0.28  # BW rewrite match successes           : 19
% 0.11/0.28  # Condensation attempts                : 0
% 0.11/0.28  # Condensation successes               : 0
% 0.11/0.28  # Termbank termtop insertions          : 10927
% 0.11/0.28  
% 0.11/0.28  # -------------------------------------------------
% 0.11/0.28  # User time                : 0.023 s
% 0.11/0.28  # System time              : 0.003 s
% 0.11/0.28  # Total time               : 0.026 s
% 0.11/0.28  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
