%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:03 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 545 expanded)
%              Number of clauses        :   55 ( 242 expanded)
%              Number of leaves         :   11 ( 139 expanded)
%              Depth                    :   25
%              Number of atoms          :  206 (1368 expanded)
%              Number of equality atoms :   46 ( 426 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t109_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t152_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t123_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | r1_tarski(k4_xboole_0(X8,X10),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_15,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | k10_relat_1(X21,k6_subset_1(X19,X20)) = k6_subset_1(k10_relat_1(X21,X19),k10_relat_1(X21,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

fof(c_0_16,plain,(
    ! [X12,X13] : k6_subset_1(X12,X13) = k4_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_17,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

fof(c_0_24,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ r1_tarski(X24,k1_relat_1(X25))
      | r1_tarski(X24,k10_relat_1(X25,k9_relat_1(X25,X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

fof(c_0_25,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | r1_tarski(k10_relat_1(X15,X14),k1_relat_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | k10_relat_1(X1,k4_xboole_0(X2,X3)) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_28])).

cnf(c_0_33,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_27]),c_0_23])).

cnf(c_0_34,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k9_relat_1(X1,k10_relat_1(X1,X2))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(k10_relat_1(X1,k1_xboole_0),k10_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,k9_relat_1(X1,k10_relat_1(X1,X2)))) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_34])).

fof(c_0_37,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | r1_tarski(k9_relat_1(X23,k10_relat_1(X23,X22)),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t152_funct_1])).

cnf(c_0_39,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(X1,k1_xboole_0),X2),k10_relat_1(X1,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_35])).

cnf(c_0_40,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,k9_relat_1(X1,k10_relat_1(X1,X2)))) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_36])).

fof(c_0_41,plain,(
    ! [X11] : k4_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_42,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_43,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v2_funct_1(esk2_0)
    & ~ r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).

cnf(c_0_44,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(X1,k1_xboole_0),X2),k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k9_relat_1(X1,k10_relat_1(X1,X2)),X2) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k10_relat_1(X1,k1_xboole_0),X2) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_44]),c_0_45])).

cnf(c_0_50,plain,
    ( r1_tarski(k10_relat_1(X1,k9_relat_1(X2,k10_relat_1(X2,X3))),k10_relat_1(X1,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_46]),c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_47]),c_0_48])])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_53,plain,
    ( r1_tarski(k10_relat_1(X1,k1_xboole_0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k9_relat_1(X1,k10_relat_1(X1,k1_xboole_0))),k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_47]),c_0_48])])).

cnf(c_0_55,plain,
    ( X1 = k10_relat_1(X2,k1_xboole_0)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k10_relat_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(X1,k10_relat_1(X1,k1_xboole_0))) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_54]),c_0_45])).

cnf(c_0_57,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k10_relat_1(X2,k1_xboole_0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(X1,k10_relat_1(X2,k1_xboole_0))) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(X1,k1_xboole_0)) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_51]),c_0_47]),c_0_48])])).

cnf(c_0_60,negated_conjecture,
    ( k10_relat_1(esk2_0,k4_xboole_0(X1,k9_relat_1(X2,k1_xboole_0))) = k10_relat_1(esk2_0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_59]),c_0_45]),c_0_47]),c_0_48])])).

fof(c_0_61,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | ~ v2_funct_1(X18)
      | k9_relat_1(X18,k6_subset_1(X16,X17)) = k6_subset_1(k9_relat_1(X18,X16),k9_relat_1(X18,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)))) = k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_60]),c_0_48])])).

cnf(c_0_63,plain,
    ( k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( k10_relat_1(esk2_0,k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)))) = k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_62]),c_0_47]),c_0_48])])).

cnf(c_0_65,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_21]),c_0_21])).

cnf(c_0_66,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_67,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(X1,X2),X3),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_30])).

cnf(c_0_68,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,k4_xboole_0(X1,k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1))))) = k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_47]),c_0_48])])).

cnf(c_0_69,plain,
    ( k9_relat_1(X1,k4_xboole_0(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)) = k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_46])).

cnf(c_0_70,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(X1,X2),X3),k10_relat_1(X1,k9_relat_1(X1,k4_xboole_0(k10_relat_1(X1,X2),X3))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1))) = k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_51]),c_0_45]),c_0_66]),c_0_47]),c_0_48])])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1),k1_xboole_0)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_48])])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1) = k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_72]),c_0_45])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_47]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 10:39:04 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.51  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4c
% 0.20/0.51  # and selection function SelectCQPrecWNTNp.
% 0.20/0.51  #
% 0.20/0.51  # Preprocessing time       : 0.026 s
% 0.20/0.51  # Presaturation interreduction done
% 0.20/0.51  
% 0.20/0.51  # Proof found!
% 0.20/0.51  # SZS status Theorem
% 0.20/0.51  # SZS output start CNFRefutation
% 0.20/0.51  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.51  fof(t109_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 0.20/0.51  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.51  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 0.20/0.51  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.20/0.51  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 0.20/0.51  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.20/0.51  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.20/0.51  fof(t152_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 0.20/0.51  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.51  fof(t123_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 0.20/0.51  fof(c_0_11, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.51  fof(c_0_12, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|r1_tarski(k4_xboole_0(X8,X10),X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).
% 0.20/0.51  cnf(c_0_13, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.51  fof(c_0_14, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.51  fof(c_0_15, plain, ![X19, X20, X21]:(~v1_relat_1(X21)|~v1_funct_1(X21)|k10_relat_1(X21,k6_subset_1(X19,X20))=k6_subset_1(k10_relat_1(X21,X19),k10_relat_1(X21,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 0.20/0.51  fof(c_0_16, plain, ![X12, X13]:k6_subset_1(X12,X13)=k4_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.20/0.51  cnf(c_0_17, plain, (r1_tarski(k4_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.51  cnf(c_0_18, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_13])).
% 0.20/0.51  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.51  cnf(c_0_20, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.51  cnf(c_0_21, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.51  cnf(c_0_22, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.51  cnf(c_0_23, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.20/0.51  fof(c_0_24, plain, ![X24, X25]:(~v1_relat_1(X25)|(~r1_tarski(X24,k1_relat_1(X25))|r1_tarski(X24,k10_relat_1(X25,k9_relat_1(X25,X24))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.20/0.51  fof(c_0_25, plain, ![X14, X15]:(~v1_relat_1(X15)|r1_tarski(k10_relat_1(X15,X14),k1_relat_1(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.20/0.51  cnf(c_0_26, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.51  cnf(c_0_27, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_21])).
% 0.20/0.51  cnf(c_0_28, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.51  cnf(c_0_29, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.51  cnf(c_0_30, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.51  cnf(c_0_31, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|k10_relat_1(X1,k4_xboole_0(X2,X3))!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.51  cnf(c_0_32, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_28])).
% 0.20/0.51  cnf(c_0_33, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_27]), c_0_23])).
% 0.20/0.51  cnf(c_0_34, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k9_relat_1(X1,k10_relat_1(X1,X2))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.51  cnf(c_0_35, plain, (r1_tarski(k10_relat_1(X1,k1_xboole_0),k10_relat_1(X1,X2))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.20/0.51  cnf(c_0_36, plain, (k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,k9_relat_1(X1,k10_relat_1(X1,X2))))=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_34])).
% 0.20/0.51  fof(c_0_37, plain, ![X22, X23]:(~v1_relat_1(X23)|~v1_funct_1(X23)|r1_tarski(k9_relat_1(X23,k10_relat_1(X23,X22)),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.20/0.51  fof(c_0_38, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1)))), inference(assume_negation,[status(cth)],[t152_funct_1])).
% 0.20/0.51  cnf(c_0_39, plain, (r1_tarski(k4_xboole_0(k10_relat_1(X1,k1_xboole_0),X2),k10_relat_1(X1,X3))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_35])).
% 0.20/0.51  cnf(c_0_40, plain, (k10_relat_1(X1,k4_xboole_0(X2,k9_relat_1(X1,k10_relat_1(X1,X2))))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_36])).
% 0.20/0.51  fof(c_0_41, plain, ![X11]:k4_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.51  cnf(c_0_42, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.51  fof(c_0_43, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(v2_funct_1(esk2_0)&~r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).
% 0.20/0.51  cnf(c_0_44, plain, (r1_tarski(k4_xboole_0(k10_relat_1(X1,k1_xboole_0),X2),k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.51  cnf(c_0_45, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.51  cnf(c_0_46, plain, (k4_xboole_0(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_42])).
% 0.20/0.51  cnf(c_0_47, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.51  cnf(c_0_48, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.51  cnf(c_0_49, plain, (k4_xboole_0(k10_relat_1(X1,k1_xboole_0),X2)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_44]), c_0_45])).
% 0.20/0.51  cnf(c_0_50, plain, (r1_tarski(k10_relat_1(X1,k9_relat_1(X2,k10_relat_1(X2,X3))),k10_relat_1(X1,X3))|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_46]), c_0_33])).
% 0.20/0.51  cnf(c_0_51, negated_conjecture, (k10_relat_1(esk2_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_47]), c_0_48])])).
% 0.20/0.51  cnf(c_0_52, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.51  cnf(c_0_53, plain, (r1_tarski(k10_relat_1(X1,k1_xboole_0),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_49])).
% 0.20/0.51  cnf(c_0_54, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k9_relat_1(X1,k10_relat_1(X1,k1_xboole_0))),k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_47]), c_0_48])])).
% 0.20/0.51  cnf(c_0_55, plain, (X1=k10_relat_1(X2,k1_xboole_0)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r1_tarski(X1,k10_relat_1(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.51  cnf(c_0_56, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(X1,k10_relat_1(X1,k1_xboole_0)))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_54]), c_0_45])).
% 0.20/0.51  cnf(c_0_57, plain, (k10_relat_1(X1,k1_xboole_0)=k10_relat_1(X2,k1_xboole_0)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_53])).
% 0.20/0.51  cnf(c_0_58, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(X1,k10_relat_1(X2,k1_xboole_0)))=k1_xboole_0|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.51  cnf(c_0_59, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(X1,k1_xboole_0))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_51]), c_0_47]), c_0_48])])).
% 0.20/0.51  cnf(c_0_60, negated_conjecture, (k10_relat_1(esk2_0,k4_xboole_0(X1,k9_relat_1(X2,k1_xboole_0)))=k10_relat_1(esk2_0,X1)|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_59]), c_0_45]), c_0_47]), c_0_48])])).
% 0.20/0.51  fof(c_0_61, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|~v1_funct_1(X18)|(~v2_funct_1(X18)|k9_relat_1(X18,k6_subset_1(X16,X17))=k6_subset_1(k9_relat_1(X18,X16),k9_relat_1(X18,X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).
% 0.20/0.51  cnf(c_0_62, negated_conjecture, (k4_xboole_0(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1))))=k1_xboole_0|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_60]), c_0_48])])).
% 0.20/0.51  cnf(c_0_63, plain, (k9_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.51  cnf(c_0_64, negated_conjecture, (k10_relat_1(esk2_0,k4_xboole_0(X1,k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1))))=k1_xboole_0|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_62]), c_0_47]), c_0_48])])).
% 0.20/0.51  cnf(c_0_65, plain, (k9_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_21]), c_0_21])).
% 0.20/0.51  cnf(c_0_66, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.51  cnf(c_0_67, plain, (r1_tarski(k4_xboole_0(k10_relat_1(X1,X2),X3),k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_30])).
% 0.20/0.51  cnf(c_0_68, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(esk2_0,k4_xboole_0(X1,k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)))))=k1_xboole_0|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_47]), c_0_48])])).
% 0.20/0.51  cnf(c_0_69, plain, (k9_relat_1(X1,k4_xboole_0(k10_relat_1(X1,k9_relat_1(X1,X2)),X2))=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_46])).
% 0.20/0.51  cnf(c_0_70, plain, (r1_tarski(k4_xboole_0(k10_relat_1(X1,X2),X3),k10_relat_1(X1,k9_relat_1(X1,k4_xboole_0(k10_relat_1(X1,X2),X3))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_67])).
% 0.20/0.51  cnf(c_0_71, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(esk2_0,k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)))=k1_xboole_0|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_51]), c_0_45]), c_0_66]), c_0_47]), c_0_48])])).
% 0.20/0.51  cnf(c_0_72, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1),k1_xboole_0)|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_48])])).
% 0.20/0.51  cnf(c_0_73, negated_conjecture, (k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)=k1_xboole_0|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_72]), c_0_45])).
% 0.20/0.51  cnf(c_0_74, negated_conjecture, (~r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.51  cnf(c_0_75, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_26, c_0_73])).
% 0.20/0.51  cnf(c_0_76, negated_conjecture, (~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.51  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_47]), c_0_48])]), ['proof']).
% 0.20/0.51  # SZS output end CNFRefutation
% 0.20/0.51  # Proof object total steps             : 78
% 0.20/0.51  # Proof object clause steps            : 55
% 0.20/0.51  # Proof object formula steps           : 23
% 0.20/0.51  # Proof object conjectures             : 22
% 0.20/0.51  # Proof object clause conjectures      : 19
% 0.20/0.51  # Proof object formula conjectures     : 3
% 0.20/0.51  # Proof object initial clauses used    : 16
% 0.20/0.51  # Proof object initial formulas used   : 11
% 0.20/0.51  # Proof object generating inferences   : 36
% 0.20/0.51  # Proof object simplifying inferences  : 42
% 0.20/0.51  # Training examples: 0 positive, 0 negative
% 0.20/0.51  # Parsed axioms                        : 11
% 0.20/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.51  # Initial clauses                      : 17
% 0.20/0.51  # Removed in clause preprocessing      : 1
% 0.20/0.51  # Initial clauses in saturation        : 16
% 0.20/0.51  # Processed clauses                    : 1556
% 0.20/0.51  # ...of these trivial                  : 4
% 0.20/0.51  # ...subsumed                          : 1269
% 0.20/0.51  # ...remaining for further processing  : 283
% 0.20/0.51  # Other redundant clauses eliminated   : 3
% 0.20/0.51  # Clauses deleted for lack of memory   : 0
% 0.20/0.51  # Backward-subsumed                    : 215
% 0.20/0.51  # Backward-rewritten                   : 1
% 0.20/0.51  # Generated clauses                    : 9024
% 0.20/0.51  # ...of the previous two non-trivial   : 6350
% 0.20/0.51  # Contextual simplify-reflections      : 12
% 0.20/0.51  # Paramodulations                      : 9021
% 0.20/0.51  # Factorizations                       : 0
% 0.20/0.51  # Equation resolutions                 : 3
% 0.20/0.51  # Propositional unsat checks           : 0
% 0.20/0.51  #    Propositional check models        : 0
% 0.20/0.51  #    Propositional check unsatisfiable : 0
% 0.20/0.51  #    Propositional clauses             : 0
% 0.20/0.51  #    Propositional clauses after purity: 0
% 0.20/0.51  #    Propositional unsat core size     : 0
% 0.20/0.51  #    Propositional preprocessing time  : 0.000
% 0.20/0.51  #    Propositional encoding time       : 0.000
% 0.20/0.51  #    Propositional solver time         : 0.000
% 0.20/0.51  #    Success case prop preproc time    : 0.000
% 0.20/0.51  #    Success case prop encoding time   : 0.000
% 0.20/0.51  #    Success case prop solver time     : 0.000
% 0.20/0.51  # Current number of processed clauses  : 50
% 0.20/0.51  #    Positive orientable unit clauses  : 17
% 0.20/0.51  #    Positive unorientable unit clauses: 0
% 0.20/0.51  #    Negative unit clauses             : 1
% 0.20/0.51  #    Non-unit-clauses                  : 32
% 0.20/0.51  # Current number of unprocessed clauses: 4753
% 0.20/0.51  # ...number of literals in the above   : 28005
% 0.20/0.51  # Current number of archived formulas  : 0
% 0.20/0.51  # Current number of archived clauses   : 232
% 0.20/0.51  # Clause-clause subsumption calls (NU) : 10213
% 0.20/0.51  # Rec. Clause-clause subsumption calls : 4696
% 0.20/0.51  # Non-unit clause-clause subsumptions  : 1496
% 0.20/0.51  # Unit Clause-clause subsumption calls : 3
% 0.20/0.51  # Rewrite failures with RHS unbound    : 0
% 0.20/0.51  # BW rewrite match attempts            : 13
% 0.20/0.51  # BW rewrite match successes           : 1
% 0.20/0.51  # Condensation attempts                : 0
% 0.20/0.51  # Condensation successes               : 0
% 0.20/0.51  # Termbank termtop insertions          : 164806
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.171 s
% 0.20/0.51  # System time              : 0.004 s
% 0.20/0.51  # Total time               : 0.175 s
% 0.20/0.51  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
