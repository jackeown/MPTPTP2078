%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:02 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 178 expanded)
%              Number of clauses        :   53 (  76 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  164 ( 373 expanded)
%              Number of equality atoms :   50 (  91 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t152_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t178_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t170_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t123_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(c_0_19,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_20,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_21,plain,(
    ! [X25] : k4_xboole_0(k1_xboole_0,X25) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X18] : k4_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_25,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(k2_xboole_0(X10,X11),X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_26,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_27,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

fof(c_0_35,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,k2_xboole_0(X21,X22))
      | r1_tarski(k4_xboole_0(X20,X21),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k2_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t152_funct_1])).

fof(c_0_39,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k2_xboole_0(X13,X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_40,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_42,plain,(
    ! [X28] :
      ( ~ v1_relat_1(X28)
      | k10_relat_1(X28,k2_relat_1(X28)) = k1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_43,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v2_funct_1(esk2_0)
    & ~ r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).

fof(c_0_44,plain,(
    ! [X34,X35,X36] :
      ( ~ v1_relat_1(X36)
      | ~ r1_tarski(X34,X35)
      | r1_tarski(k10_relat_1(X36,X34),k10_relat_1(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).

fof(c_0_45,plain,(
    ! [X15] : r1_tarski(k1_xboole_0,X15) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_48,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | r1_tarski(k10_relat_1(X30,X29),k10_relat_1(X30,k2_relat_1(X30))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).

cnf(c_0_49,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_51,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X44)
      | ~ v1_funct_1(X44)
      | r1_tarski(k9_relat_1(X44,k10_relat_1(X44,X43)),X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_52,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_relat_1(X39)
      | ~ v1_funct_1(X39)
      | ~ v2_funct_1(X39)
      | k9_relat_1(X39,k6_subset_1(X37,X38)) = k6_subset_1(k9_relat_1(X39,X37),k9_relat_1(X39,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).

fof(c_0_53,plain,(
    ! [X26,X27] : k6_subset_1(X26,X27) = k4_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_54,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_56,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_relat_1(X42)
      | ~ v1_funct_1(X42)
      | k10_relat_1(X42,k6_subset_1(X40,X41)) = k6_subset_1(k10_relat_1(X42,X40),k10_relat_1(X42,X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

fof(c_0_57,plain,(
    ! [X45,X46] :
      ( ~ v1_relat_1(X46)
      | ~ r1_tarski(X45,k1_relat_1(X46))
      | r1_tarski(X45,k10_relat_1(X46,k9_relat_1(X46,X45))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_32])).

cnf(c_0_59,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( k10_relat_1(esk2_0,k2_relat_1(esk2_0)) = k1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_63,plain,
    ( k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( r1_tarski(k10_relat_1(X1,k1_xboole_0),k10_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_66,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_50]),c_0_60])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_50])])).

cnf(c_0_72,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k1_xboole_0),k10_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_50])).

cnf(c_0_75,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_64]),c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)))
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_50])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,X1),X2),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(k9_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X2)) = k9_relat_1(esk2_0,k4_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_62]),c_0_50])])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk2_0,k1_xboole_0),k10_relat_1(esk2_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,X2)) = k10_relat_1(esk2_0,k4_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_50]),c_0_62])])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,X1),X2),k10_relat_1(esk2_0,k9_relat_1(esk2_0,k4_xboole_0(k10_relat_1(esk2_0,X1),X2)))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( k9_relat_1(esk2_0,k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81]),c_0_28])).

cnf(c_0_85,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_46,c_0_55])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_87,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_85,c_0_32])).

cnf(c_0_88,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_86]),c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.61/0.79  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05DN
% 0.61/0.79  # and selection function SelectDivLits.
% 0.61/0.79  #
% 0.61/0.79  # Preprocessing time       : 0.027 s
% 0.61/0.79  # Presaturation interreduction done
% 0.61/0.79  
% 0.61/0.79  # Proof found!
% 0.61/0.79  # SZS status Theorem
% 0.61/0.79  # SZS output start CNFRefutation
% 0.61/0.79  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.61/0.79  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.61/0.79  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.61/0.79  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.61/0.79  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.61/0.79  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.61/0.79  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.61/0.79  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.61/0.79  fof(t152_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 0.61/0.79  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.61/0.79  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.61/0.79  fof(t178_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 0.61/0.79  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.61/0.79  fof(t170_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t170_relat_1)).
% 0.61/0.79  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.61/0.79  fof(t123_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 0.61/0.79  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.61/0.79  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 0.61/0.79  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 0.61/0.79  fof(c_0_19, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.61/0.79  fof(c_0_20, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.61/0.79  fof(c_0_21, plain, ![X25]:k4_xboole_0(k1_xboole_0,X25)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.61/0.79  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.61/0.79  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.61/0.79  fof(c_0_24, plain, ![X18]:k4_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.61/0.79  fof(c_0_25, plain, ![X10, X11, X12]:(~r1_tarski(k2_xboole_0(X10,X11),X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.61/0.79  fof(c_0_26, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.61/0.79  fof(c_0_27, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.61/0.79  cnf(c_0_28, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.61/0.79  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_23])).
% 0.61/0.79  cnf(c_0_30, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.61/0.79  cnf(c_0_31, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.61/0.79  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.61/0.79  cnf(c_0_33, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.61/0.79  cnf(c_0_34, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.61/0.79  fof(c_0_35, plain, ![X20, X21, X22]:(~r1_tarski(X20,k2_xboole_0(X21,X22))|r1_tarski(k4_xboole_0(X20,X21),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.61/0.79  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~r1_tarski(k2_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.61/0.79  cnf(c_0_37, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.61/0.79  fof(c_0_38, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1)))), inference(assume_negation,[status(cth)],[t152_funct_1])).
% 0.61/0.79  fof(c_0_39, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k2_xboole_0(X13,X14)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.61/0.79  cnf(c_0_40, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.61/0.79  cnf(c_0_41, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.61/0.79  fof(c_0_42, plain, ![X28]:(~v1_relat_1(X28)|k10_relat_1(X28,k2_relat_1(X28))=k1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.61/0.79  fof(c_0_43, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(v2_funct_1(esk2_0)&~r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).
% 0.61/0.79  fof(c_0_44, plain, ![X34, X35, X36]:(~v1_relat_1(X36)|(~r1_tarski(X34,X35)|r1_tarski(k10_relat_1(X36,X34),k10_relat_1(X36,X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).
% 0.61/0.79  fof(c_0_45, plain, ![X15]:r1_tarski(k1_xboole_0,X15), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.61/0.79  cnf(c_0_46, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.61/0.79  cnf(c_0_47, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.61/0.79  fof(c_0_48, plain, ![X29, X30]:(~v1_relat_1(X30)|r1_tarski(k10_relat_1(X30,X29),k10_relat_1(X30,k2_relat_1(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t170_relat_1])])).
% 0.61/0.79  cnf(c_0_49, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.61/0.79  cnf(c_0_50, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.61/0.79  fof(c_0_51, plain, ![X43, X44]:(~v1_relat_1(X44)|~v1_funct_1(X44)|r1_tarski(k9_relat_1(X44,k10_relat_1(X44,X43)),X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.61/0.79  fof(c_0_52, plain, ![X37, X38, X39]:(~v1_relat_1(X39)|~v1_funct_1(X39)|(~v2_funct_1(X39)|k9_relat_1(X39,k6_subset_1(X37,X38))=k6_subset_1(k9_relat_1(X39,X37),k9_relat_1(X39,X38)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).
% 0.61/0.79  fof(c_0_53, plain, ![X26, X27]:k6_subset_1(X26,X27)=k4_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.61/0.79  cnf(c_0_54, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.61/0.79  cnf(c_0_55, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.61/0.79  fof(c_0_56, plain, ![X40, X41, X42]:(~v1_relat_1(X42)|~v1_funct_1(X42)|k10_relat_1(X42,k6_subset_1(X40,X41))=k6_subset_1(k10_relat_1(X42,X40),k10_relat_1(X42,X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 0.61/0.79  fof(c_0_57, plain, ![X45, X46]:(~v1_relat_1(X46)|(~r1_tarski(X45,k1_relat_1(X46))|r1_tarski(X45,k10_relat_1(X46,k9_relat_1(X46,X45))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.61/0.79  cnf(c_0_58, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_32])).
% 0.61/0.79  cnf(c_0_59, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.61/0.79  cnf(c_0_60, negated_conjecture, (k10_relat_1(esk2_0,k2_relat_1(esk2_0))=k1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.61/0.79  cnf(c_0_61, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.61/0.79  cnf(c_0_62, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.61/0.79  cnf(c_0_63, plain, (k9_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.61/0.79  cnf(c_0_64, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.61/0.79  cnf(c_0_65, plain, (r1_tarski(k10_relat_1(X1,k1_xboole_0),k10_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.61/0.79  cnf(c_0_66, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.61/0.79  cnf(c_0_67, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.61/0.79  cnf(c_0_68, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_36, c_0_58])).
% 0.61/0.79  cnf(c_0_69, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_50]), c_0_60])).
% 0.61/0.79  cnf(c_0_70, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.61/0.79  cnf(c_0_71, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_50])])).
% 0.61/0.79  cnf(c_0_72, plain, (k9_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_64])).
% 0.61/0.79  cnf(c_0_73, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.61/0.79  cnf(c_0_74, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k1_xboole_0),k10_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_65, c_0_50])).
% 0.61/0.79  cnf(c_0_75, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_64]), c_0_64])).
% 0.61/0.79  cnf(c_0_76, negated_conjecture, (r1_tarski(X1,k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)))|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_67, c_0_50])).
% 0.61/0.79  cnf(c_0_77, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,X1),X2),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.61/0.79  cnf(c_0_78, negated_conjecture, (k4_xboole_0(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.61/0.79  cnf(c_0_79, negated_conjecture, (k4_xboole_0(k9_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X2))=k9_relat_1(esk2_0,k4_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_62]), c_0_50])])).
% 0.61/0.79  cnf(c_0_80, negated_conjecture, (k4_xboole_0(k10_relat_1(esk2_0,k1_xboole_0),k10_relat_1(esk2_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_74])).
% 0.61/0.79  cnf(c_0_81, negated_conjecture, (k4_xboole_0(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,X2))=k10_relat_1(esk2_0,k4_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_50]), c_0_62])])).
% 0.61/0.79  cnf(c_0_82, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,X1),X2),k10_relat_1(esk2_0,k9_relat_1(esk2_0,k4_xboole_0(k10_relat_1(esk2_0,X1),X2))))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.61/0.79  cnf(c_0_83, negated_conjecture, (k9_relat_1(esk2_0,k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.61/0.79  cnf(c_0_84, negated_conjecture, (k10_relat_1(esk2_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81]), c_0_28])).
% 0.61/0.79  cnf(c_0_85, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_46, c_0_55])).
% 0.61/0.79  cnf(c_0_86, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])).
% 0.61/0.79  cnf(c_0_87, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_85, c_0_32])).
% 0.61/0.79  cnf(c_0_88, negated_conjecture, (k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_86]), c_0_87])).
% 0.61/0.79  cnf(c_0_89, negated_conjecture, (~r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.61/0.79  cnf(c_0_90, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)), inference(spm,[status(thm)],[c_0_33, c_0_88])).
% 0.61/0.79  cnf(c_0_91, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90])]), ['proof']).
% 0.61/0.79  # SZS output end CNFRefutation
% 0.61/0.79  # Proof object total steps             : 92
% 0.61/0.79  # Proof object clause steps            : 53
% 0.61/0.79  # Proof object formula steps           : 39
% 0.61/0.79  # Proof object conjectures             : 24
% 0.61/0.79  # Proof object clause conjectures      : 21
% 0.61/0.79  # Proof object formula conjectures     : 3
% 0.61/0.79  # Proof object initial clauses used    : 23
% 0.61/0.79  # Proof object initial formulas used   : 19
% 0.61/0.79  # Proof object generating inferences   : 25
% 0.61/0.79  # Proof object simplifying inferences  : 22
% 0.61/0.79  # Training examples: 0 positive, 0 negative
% 0.61/0.79  # Parsed axioms                        : 22
% 0.61/0.79  # Removed by relevancy pruning/SinE    : 0
% 0.61/0.79  # Initial clauses                      : 26
% 0.61/0.79  # Removed in clause preprocessing      : 2
% 0.61/0.79  # Initial clauses in saturation        : 24
% 0.61/0.79  # Processed clauses                    : 3049
% 0.61/0.79  # ...of these trivial                  : 607
% 0.61/0.79  # ...subsumed                          : 1559
% 0.61/0.79  # ...remaining for further processing  : 883
% 0.61/0.79  # Other redundant clauses eliminated   : 30
% 0.61/0.79  # Clauses deleted for lack of memory   : 0
% 0.61/0.79  # Backward-subsumed                    : 15
% 0.61/0.79  # Backward-rewritten                   : 121
% 0.61/0.79  # Generated clauses                    : 54275
% 0.61/0.79  # ...of the previous two non-trivial   : 27093
% 0.61/0.79  # Contextual simplify-reflections      : 0
% 0.61/0.79  # Paramodulations                      : 54245
% 0.61/0.79  # Factorizations                       : 0
% 0.61/0.79  # Equation resolutions                 : 30
% 0.61/0.79  # Propositional unsat checks           : 0
% 0.61/0.79  #    Propositional check models        : 0
% 0.61/0.79  #    Propositional check unsatisfiable : 0
% 0.61/0.79  #    Propositional clauses             : 0
% 0.61/0.79  #    Propositional clauses after purity: 0
% 0.61/0.79  #    Propositional unsat core size     : 0
% 0.61/0.79  #    Propositional preprocessing time  : 0.000
% 0.61/0.79  #    Propositional encoding time       : 0.000
% 0.61/0.79  #    Propositional solver time         : 0.000
% 0.61/0.79  #    Success case prop preproc time    : 0.000
% 0.61/0.79  #    Success case prop encoding time   : 0.000
% 0.61/0.79  #    Success case prop solver time     : 0.000
% 0.61/0.79  # Current number of processed clauses  : 723
% 0.61/0.79  #    Positive orientable unit clauses  : 514
% 0.61/0.79  #    Positive unorientable unit clauses: 2
% 0.61/0.79  #    Negative unit clauses             : 0
% 0.61/0.79  #    Non-unit-clauses                  : 207
% 0.61/0.79  # Current number of unprocessed clauses: 23681
% 0.61/0.79  # ...number of literals in the above   : 26546
% 0.61/0.79  # Current number of archived formulas  : 0
% 0.61/0.79  # Current number of archived clauses   : 162
% 0.61/0.79  # Clause-clause subsumption calls (NU) : 22216
% 0.61/0.79  # Rec. Clause-clause subsumption calls : 19228
% 0.61/0.79  # Non-unit clause-clause subsumptions  : 1570
% 0.61/0.79  # Unit Clause-clause subsumption calls : 462
% 0.61/0.79  # Rewrite failures with RHS unbound    : 0
% 0.61/0.79  # BW rewrite match attempts            : 3726
% 0.61/0.79  # BW rewrite match successes           : 87
% 0.61/0.79  # Condensation attempts                : 0
% 0.61/0.79  # Condensation successes               : 0
% 0.61/0.79  # Termbank termtop insertions          : 906092
% 0.61/0.79  
% 0.61/0.79  # -------------------------------------------------
% 0.61/0.79  # User time                : 0.433 s
% 0.61/0.79  # System time              : 0.021 s
% 0.61/0.79  # Total time               : 0.455 s
% 0.61/0.79  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
