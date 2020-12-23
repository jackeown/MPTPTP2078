%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:53 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 143 expanded)
%              Number of clauses        :   36 (  58 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  147 ( 276 expanded)
%              Number of equality atoms :   60 ( 128 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t173_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(t147_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t170_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

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

fof(c_0_18,plain,(
    ! [X28,X29] : k1_setfam_1(k2_tarski(X28,X29)) = k3_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_19,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_xboole_0(X13,X14)
      | r1_xboole_0(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_21,plain,(
    ! [X33,X34] :
      ( ( k10_relat_1(X34,X33) != k1_xboole_0
        | r1_xboole_0(k2_relat_1(X34),X33)
        | ~ v1_relat_1(X34) )
      & ( ~ r1_xboole_0(k2_relat_1(X34),X33)
        | k10_relat_1(X34,X33) = k1_xboole_0
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,k2_relat_1(X2))
         => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t147_funct_1])).

fof(c_0_23,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X22,X23,X24,X25] : k3_enumset1(X22,X22,X23,X24,X25) = k2_enumset1(X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r1_xboole_0(k2_relat_1(X1),X2)
    | k10_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r1_tarski(esk1_0,k2_relat_1(esk2_0))
    & k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ v1_funct_1(X37)
      | k10_relat_1(X37,k6_subset_1(X35,X36)) = k6_subset_1(k10_relat_1(X37,X35),k10_relat_1(X37,X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

fof(c_0_38,plain,(
    ! [X26,X27] : k6_subset_1(X26,X27) = k4_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_39,plain,(
    ! [X15,X16] :
      ( ( ~ r1_xboole_0(X15,X16)
        | k4_xboole_0(X15,X16) = X15 )
      & ( k4_xboole_0(X15,X16) != X15
        | r1_xboole_0(X15,X16) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,X2)
    | k10_relat_1(X3,X2) != k1_xboole_0
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k2_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk1_0,k2_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) = k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_33]),c_0_34]),c_0_35])).

fof(c_0_45,plain,(
    ! [X7,X8] :
      ( ( k4_xboole_0(X7,X8) != k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | k4_xboole_0(X7,X8) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_46,plain,(
    ! [X9] : k4_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_47,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_49,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | r1_tarski(k10_relat_1(X32,X31),k10_relat_1(X32,k2_relat_1(X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).

fof(c_0_50,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | k10_relat_1(X30,k2_relat_1(X30)) = k1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | k10_relat_1(esk2_0,X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_44])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_48])).

fof(c_0_57,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X41)
      | ~ r1_tarski(X40,k1_relat_1(X41))
      | r1_tarski(X40,k10_relat_1(X41,k9_relat_1(X41,X40))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_58,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(esk1_0,X1) = esk1_0
    | k10_relat_1(esk2_0,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_62,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_56])).

cnf(c_0_63,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( X1 = esk1_0
    | k10_relat_1(esk2_0,k4_xboole_0(esk1_0,X1)) != k1_xboole_0
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,k9_relat_1(X1,k10_relat_1(X1,X2)))) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_68,negated_conjecture,
    ( k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_69,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | ~ v1_funct_1(X39)
      | r1_tarski(k9_relat_1(X39,k10_relat_1(X39,X38)),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_42])]),c_0_68])).

cnf(c_0_71,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_67]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.37/0.61  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.37/0.61  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.37/0.61  #
% 0.37/0.61  # Preprocessing time       : 0.028 s
% 0.37/0.61  # Presaturation interreduction done
% 0.37/0.61  
% 0.37/0.61  # Proof found!
% 0.37/0.61  # SZS status Theorem
% 0.37/0.61  # SZS output start CNFRefutation
% 0.37/0.61  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.37/0.61  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.37/0.61  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.37/0.61  fof(t173_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.37/0.61  fof(t147_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 0.37/0.61  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.37/0.61  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.37/0.61  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.37/0.61  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.37/0.61  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 0.37/0.61  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.37/0.61  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.37/0.61  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.37/0.61  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.37/0.61  fof(t170_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 0.37/0.61  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.37/0.61  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.37/0.61  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.37/0.61  fof(c_0_18, plain, ![X28, X29]:k1_setfam_1(k2_tarski(X28,X29))=k3_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.37/0.61  fof(c_0_19, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.37/0.61  fof(c_0_20, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_xboole_0(X13,X14)|r1_xboole_0(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.37/0.61  fof(c_0_21, plain, ![X33, X34]:((k10_relat_1(X34,X33)!=k1_xboole_0|r1_xboole_0(k2_relat_1(X34),X33)|~v1_relat_1(X34))&(~r1_xboole_0(k2_relat_1(X34),X33)|k10_relat_1(X34,X33)=k1_xboole_0|~v1_relat_1(X34))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).
% 0.37/0.61  fof(c_0_22, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1))), inference(assume_negation,[status(cth)],[t147_funct_1])).
% 0.37/0.61  fof(c_0_23, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.37/0.61  cnf(c_0_24, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.61  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.37/0.61  fof(c_0_26, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.37/0.61  fof(c_0_27, plain, ![X22, X23, X24, X25]:k3_enumset1(X22,X22,X23,X24,X25)=k2_enumset1(X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.37/0.61  fof(c_0_28, plain, ![X10, X11]:k4_xboole_0(X10,k4_xboole_0(X10,X11))=k3_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.37/0.61  cnf(c_0_29, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.37/0.61  cnf(c_0_30, plain, (r1_xboole_0(k2_relat_1(X1),X2)|k10_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.37/0.61  fof(c_0_31, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(r1_tarski(esk1_0,k2_relat_1(esk2_0))&k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))!=esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.37/0.61  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.37/0.61  cnf(c_0_33, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.37/0.61  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.37/0.61  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.37/0.61  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.37/0.61  fof(c_0_37, plain, ![X35, X36, X37]:(~v1_relat_1(X37)|~v1_funct_1(X37)|k10_relat_1(X37,k6_subset_1(X35,X36))=k6_subset_1(k10_relat_1(X37,X35),k10_relat_1(X37,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 0.37/0.61  fof(c_0_38, plain, ![X26, X27]:k6_subset_1(X26,X27)=k4_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.37/0.61  fof(c_0_39, plain, ![X15, X16]:((~r1_xboole_0(X15,X16)|k4_xboole_0(X15,X16)=X15)&(k4_xboole_0(X15,X16)!=X15|r1_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.37/0.61  cnf(c_0_40, plain, (r1_xboole_0(X1,X2)|k10_relat_1(X3,X2)!=k1_xboole_0|~v1_relat_1(X3)|~r1_tarski(X1,k2_relat_1(X3))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.37/0.61  cnf(c_0_41, negated_conjecture, (r1_tarski(esk1_0,k2_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.37/0.61  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.37/0.61  cnf(c_0_43, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))=k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35])).
% 0.37/0.61  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_33]), c_0_34]), c_0_35])).
% 0.37/0.61  fof(c_0_45, plain, ![X7, X8]:((k4_xboole_0(X7,X8)!=k1_xboole_0|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|k4_xboole_0(X7,X8)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.37/0.61  fof(c_0_46, plain, ![X9]:k4_xboole_0(X9,k1_xboole_0)=X9, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.37/0.61  cnf(c_0_47, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.37/0.61  cnf(c_0_48, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.37/0.61  fof(c_0_49, plain, ![X31, X32]:(~v1_relat_1(X32)|r1_tarski(k10_relat_1(X32,X31),k10_relat_1(X32,k2_relat_1(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).
% 0.37/0.61  fof(c_0_50, plain, ![X30]:(~v1_relat_1(X30)|k10_relat_1(X30,k2_relat_1(X30))=k1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.37/0.61  cnf(c_0_51, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.37/0.61  cnf(c_0_52, negated_conjecture, (r1_xboole_0(esk1_0,X1)|k10_relat_1(esk2_0,X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.37/0.61  cnf(c_0_53, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_44])).
% 0.37/0.61  cnf(c_0_54, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.37/0.61  cnf(c_0_55, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.37/0.61  cnf(c_0_56, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_48])).
% 0.37/0.61  fof(c_0_57, plain, ![X40, X41]:(~v1_relat_1(X41)|(~r1_tarski(X40,k1_relat_1(X41))|r1_tarski(X40,k10_relat_1(X41,k9_relat_1(X41,X40))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.37/0.61  cnf(c_0_58, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.37/0.61  cnf(c_0_59, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.37/0.61  cnf(c_0_60, negated_conjecture, (k4_xboole_0(esk1_0,X1)=esk1_0|k10_relat_1(esk2_0,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.37/0.61  cnf(c_0_61, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.37/0.61  cnf(c_0_62, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_54, c_0_56])).
% 0.37/0.61  cnf(c_0_63, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.37/0.61  cnf(c_0_64, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.37/0.61  cnf(c_0_65, negated_conjecture, (X1=esk1_0|k10_relat_1(esk2_0,k4_xboole_0(esk1_0,X1))!=k1_xboole_0|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.37/0.61  cnf(c_0_66, plain, (k10_relat_1(X1,k4_xboole_0(X2,k9_relat_1(X1,k10_relat_1(X1,X2))))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.37/0.61  cnf(c_0_67, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.37/0.61  cnf(c_0_68, negated_conjecture, (k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0))!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.37/0.61  fof(c_0_69, plain, ![X38, X39]:(~v1_relat_1(X39)|~v1_funct_1(X39)|r1_tarski(k9_relat_1(X39,k10_relat_1(X39,X38)),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.37/0.61  cnf(c_0_70, negated_conjecture, (~r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,esk1_0)),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_42])]), c_0_68])).
% 0.37/0.61  cnf(c_0_71, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.37/0.61  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_67]), c_0_42])]), ['proof']).
% 0.37/0.61  # SZS output end CNFRefutation
% 0.37/0.61  # Proof object total steps             : 73
% 0.37/0.61  # Proof object clause steps            : 36
% 0.37/0.61  # Proof object formula steps           : 37
% 0.37/0.61  # Proof object conjectures             : 12
% 0.37/0.61  # Proof object clause conjectures      : 9
% 0.37/0.61  # Proof object formula conjectures     : 3
% 0.37/0.61  # Proof object initial clauses used    : 21
% 0.37/0.61  # Proof object initial formulas used   : 18
% 0.37/0.61  # Proof object generating inferences   : 10
% 0.37/0.61  # Proof object simplifying inferences  : 25
% 0.37/0.61  # Training examples: 0 positive, 0 negative
% 0.37/0.61  # Parsed axioms                        : 18
% 0.37/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.61  # Initial clauses                      : 24
% 0.37/0.61  # Removed in clause preprocessing      : 5
% 0.37/0.61  # Initial clauses in saturation        : 19
% 0.37/0.61  # Processed clauses                    : 2906
% 0.37/0.61  # ...of these trivial                  : 124
% 0.37/0.61  # ...subsumed                          : 2118
% 0.37/0.61  # ...remaining for further processing  : 664
% 0.37/0.61  # Other redundant clauses eliminated   : 182
% 0.37/0.61  # Clauses deleted for lack of memory   : 0
% 0.37/0.61  # Backward-subsumed                    : 72
% 0.37/0.61  # Backward-rewritten                   : 44
% 0.37/0.61  # Generated clauses                    : 17762
% 0.37/0.61  # ...of the previous two non-trivial   : 15125
% 0.37/0.61  # Contextual simplify-reflections      : 70
% 0.37/0.61  # Paramodulations                      : 17580
% 0.37/0.61  # Factorizations                       : 0
% 0.37/0.61  # Equation resolutions                 : 182
% 0.37/0.61  # Propositional unsat checks           : 0
% 0.37/0.61  #    Propositional check models        : 0
% 0.37/0.61  #    Propositional check unsatisfiable : 0
% 0.37/0.61  #    Propositional clauses             : 0
% 0.37/0.61  #    Propositional clauses after purity: 0
% 0.37/0.61  #    Propositional unsat core size     : 0
% 0.37/0.61  #    Propositional preprocessing time  : 0.000
% 0.37/0.61  #    Propositional encoding time       : 0.000
% 0.37/0.61  #    Propositional solver time         : 0.000
% 0.37/0.61  #    Success case prop preproc time    : 0.000
% 0.37/0.61  #    Success case prop encoding time   : 0.000
% 0.37/0.61  #    Success case prop solver time     : 0.000
% 0.37/0.61  # Current number of processed clauses  : 529
% 0.37/0.61  #    Positive orientable unit clauses  : 23
% 0.37/0.61  #    Positive unorientable unit clauses: 3
% 0.37/0.61  #    Negative unit clauses             : 9
% 0.37/0.61  #    Non-unit-clauses                  : 494
% 0.37/0.61  # Current number of unprocessed clauses: 12056
% 0.37/0.61  # ...number of literals in the above   : 53876
% 0.37/0.61  # Current number of archived formulas  : 0
% 0.37/0.61  # Current number of archived clauses   : 140
% 0.37/0.61  # Clause-clause subsumption calls (NU) : 40161
% 0.37/0.61  # Rec. Clause-clause subsumption calls : 28945
% 0.37/0.61  # Non-unit clause-clause subsumptions  : 1897
% 0.37/0.61  # Unit Clause-clause subsumption calls : 1234
% 0.37/0.61  # Rewrite failures with RHS unbound    : 0
% 0.37/0.61  # BW rewrite match attempts            : 40
% 0.37/0.61  # BW rewrite match successes           : 22
% 0.37/0.61  # Condensation attempts                : 0
% 0.37/0.61  # Condensation successes               : 0
% 0.37/0.61  # Termbank termtop insertions          : 305010
% 0.37/0.62  
% 0.37/0.62  # -------------------------------------------------
% 0.37/0.62  # User time                : 0.260 s
% 0.37/0.62  # System time              : 0.018 s
% 0.37/0.62  # Total time               : 0.278 s
% 0.37/0.62  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
