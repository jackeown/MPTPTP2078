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
% DateTime   : Thu Dec  3 10:55:04 EST 2020

% Result     : Theorem 1.21s
% Output     : CNFRefutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  122 (1972 expanded)
%              Number of clauses        :   91 ( 801 expanded)
%              Number of leaves         :   15 ( 499 expanded)
%              Depth                    :   30
%              Number of atoms          :  301 (5454 expanded)
%              Number of equality atoms :   79 ( 993 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t152_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( X1 != k1_xboole_0
          & r1_tarski(X1,k1_relat_1(X2))
          & k9_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(t152_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

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

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t14_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(c_0_15,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | X22 = k1_xboole_0
      | ~ r1_tarski(X22,k1_relat_1(X23))
      | k9_relat_1(X23,X22) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_relat_1])])).

fof(c_0_16,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | r1_tarski(k10_relat_1(X25,X24),k1_relat_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_17,plain,(
    ! [X19] :
      ( ~ r1_tarski(X19,k1_xboole_0)
      | X19 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_18,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ v1_funct_1(X33)
      | r1_tarski(k9_relat_1(X33,k10_relat_1(X33,X32)),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_19,plain,
    ( X2 = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | k9_relat_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t152_funct_1])).

cnf(c_0_24,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | k9_relat_1(X1,k10_relat_1(X1,X2)) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,k1_xboole_0)) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v2_funct_1(esk3_0)
    & ~ r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_27,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | ~ v2_funct_1(X31)
      | k9_relat_1(X31,k6_subset_1(X29,X30)) = k6_subset_1(k9_relat_1(X31,X29),k9_relat_1(X31,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).

fof(c_0_28,plain,(
    ! [X20,X21] : k6_subset_1(X20,X21) = k4_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_29,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k10_relat_1(esk3_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

fof(c_0_35,plain,(
    ! [X7,X8] :
      ( ( k4_xboole_0(X7,X8) != k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | k4_xboole_0(X7,X8) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_36,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_34]),c_0_30]),c_0_31])])).

cnf(c_0_38,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(k9_relat_1(esk3_0,X1),k1_xboole_0) = k9_relat_1(esk3_0,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_30]),c_0_31])])).

fof(c_0_41,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,X1),k1_xboole_0)
    | k9_relat_1(esk3_0,k4_xboole_0(X1,k1_xboole_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X16] : r1_tarski(k1_xboole_0,X16) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_45,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,X1),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_37])])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | k9_relat_1(X1,k4_xboole_0(X2,X3)) != k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( k9_relat_1(esk3_0,X1) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

fof(c_0_52,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ r1_tarski(X34,k1_relat_1(X35))
      | r1_tarski(X34,k10_relat_1(X35,k9_relat_1(X35,X34))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

fof(c_0_53,plain,(
    ! [X17,X18] : r1_tarski(k4_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2))
    | ~ r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_38]),c_0_30]),c_0_31])])).

cnf(c_0_56,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,X1),X2)
    | ~ r1_tarski(k4_xboole_0(X1,k10_relat_1(esk3_0,X2)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_30]),c_0_31])])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X3,k1_relat_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_56])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,X1),X2)
    | ~ r1_tarski(X1,k10_relat_1(esk3_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_43]),c_0_48])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_64,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X3
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X3)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_59])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k10_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_20])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,X1),X2)
    | ~ r1_tarski(X1,k10_relat_1(esk3_0,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,X1),X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_47])).

cnf(c_0_70,negated_conjecture,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_51]),c_0_34]),c_0_31]),c_0_34]),c_0_48])]),c_0_63])).

cnf(c_0_71,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(X1,X2),X3),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_57])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,k4_xboole_0(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(k9_relat_1(esk3_0,X1),X2) = k9_relat_1(esk3_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k9_relat_1(esk3_0,X2))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_69])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k10_relat_1(X1,X2),X3) = k1_xboole_0
    | k9_relat_1(X1,k4_xboole_0(k10_relat_1(X1,X2),X3)) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( k9_relat_1(esk3_0,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0
    | ~ r1_tarski(k9_relat_1(esk3_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k9_relat_1(esk3_0,X3))
    | ~ r1_tarski(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1))),k9_relat_1(esk3_0,X1))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k9_relat_1(esk3_0,X1) = k1_xboole_0
    | ~ r1_tarski(X1,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X2)))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_61])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk3_0,X1),k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_31])])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1))),X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,k10_relat_1(X2,X3))),k1_relat_1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_22])).

cnf(c_0_83,negated_conjecture,
    ( k9_relat_1(esk3_0,k9_relat_1(esk3_0,X1)) = k1_xboole_0
    | ~ r1_tarski(X1,k10_relat_1(esk3_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X2))))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_61])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,X1),k1_xboole_0)
    | ~ r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1))) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_81])).

fof(c_0_86,plain,(
    ! [X9,X10,X11] :
      ( ( r1_tarski(X9,esk1_3(X9,X10,X11))
        | ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X11,X10)
        | X10 = k2_xboole_0(X9,X11) )
      & ( r1_tarski(X11,esk1_3(X9,X10,X11))
        | ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X11,X10)
        | X10 = k2_xboole_0(X9,X11) )
      & ( ~ r1_tarski(X10,esk1_3(X9,X10,X11))
        | ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X11,X10)
        | X10 = k2_xboole_0(X9,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).

cnf(c_0_87,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,k10_relat_1(X2,X3))) = k1_xboole_0
    | k9_relat_1(X2,k9_relat_1(X1,k10_relat_1(X1,k10_relat_1(X2,X3)))) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( k9_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1))))) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_67])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_48])])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,esk1_3(X2,X3,X1))
    | X3 = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_91,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,X3)) = k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_36])).

cnf(c_0_92,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)))) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_30]),c_0_31])])).

cnf(c_0_93,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_56])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_89])).

fof(c_0_95,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X28)
      | k10_relat_1(X28,k2_xboole_0(X26,X27)) = k2_xboole_0(k10_relat_1(X28,X26),k10_relat_1(X28,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

cnf(c_0_96,plain,
    ( X1 = k2_xboole_0(k1_xboole_0,X2)
    | r1_tarski(X2,esk1_3(k1_xboole_0,X1,X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_48])).

cnf(c_0_97,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,X2)) = k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_67])).

cnf(c_0_98,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_57])).

cnf(c_0_99,negated_conjecture,
    ( k10_relat_1(esk3_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1))) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_92]),c_0_31])])).

cnf(c_0_100,negated_conjecture,
    ( k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)) = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_31])]),c_0_63])).

cnf(c_0_101,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_102,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,esk1_3(X2,X1,X3))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_103,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1
    | r1_tarski(X1,esk1_3(k1_xboole_0,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_67])).

cnf(c_0_104,negated_conjecture,
    ( k9_relat_1(esk3_0,k4_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_97]),c_0_98]),c_0_38]),c_0_30]),c_0_31])])).

cnf(c_0_105,negated_conjecture,
    ( k10_relat_1(esk3_0,X1) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k10_relat_1(esk3_0,X1)) = k10_relat_1(esk3_0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_34]),c_0_31])])).

cnf(c_0_107,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_67]),c_0_48])])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,X1)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_104]),c_0_37]),c_0_38]),c_0_30]),c_0_31])])).

cnf(c_0_109,negated_conjecture,
    ( k10_relat_1(esk3_0,k2_xboole_0(X1,X2)) = k10_relat_1(esk3_0,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_105]),c_0_106]),c_0_107]),c_0_31])])).

cnf(c_0_110,negated_conjecture,
    ( k9_relat_1(esk3_0,k4_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_108]),c_0_48])])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_109]),c_0_31])])).

cnf(c_0_112,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X1)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_110]),c_0_31])])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_72])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_112]),c_0_48])])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk3_0))
    | ~ r1_tarski(X1,k10_relat_1(esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_113])).

cnf(c_0_116,negated_conjecture,
    ( k9_relat_1(esk3_0,k4_xboole_0(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_114]),c_0_38]),c_0_30]),c_0_31])])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,X1),X2),k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_57])).

cnf(c_0_118,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_116]),c_0_34]),c_0_31]),c_0_34]),c_0_48]),c_0_117])])).

cnf(c_0_119,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_118])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_120])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.21/1.44  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.21/1.44  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.21/1.44  #
% 1.21/1.44  # Preprocessing time       : 0.027 s
% 1.21/1.44  # Presaturation interreduction done
% 1.21/1.44  
% 1.21/1.44  # Proof found!
% 1.21/1.44  # SZS status Theorem
% 1.21/1.44  # SZS output start CNFRefutation
% 1.21/1.44  fof(t152_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k1_relat_1(X2)))&k9_relat_1(X2,X1)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 1.21/1.44  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.21/1.44  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.21/1.44  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 1.21/1.44  fof(t152_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 1.21/1.44  fof(t123_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 1.21/1.44  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.21/1.44  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.21/1.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.21/1.44  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.21/1.44  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.21/1.44  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 1.21/1.44  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.21/1.44  fof(t14_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 1.21/1.44  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 1.21/1.44  fof(c_0_15, plain, ![X22, X23]:(~v1_relat_1(X23)|(X22=k1_xboole_0|~r1_tarski(X22,k1_relat_1(X23))|k9_relat_1(X23,X22)!=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_relat_1])])).
% 1.21/1.44  fof(c_0_16, plain, ![X24, X25]:(~v1_relat_1(X25)|r1_tarski(k10_relat_1(X25,X24),k1_relat_1(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 1.21/1.44  fof(c_0_17, plain, ![X19]:(~r1_tarski(X19,k1_xboole_0)|X19=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 1.21/1.44  fof(c_0_18, plain, ![X32, X33]:(~v1_relat_1(X33)|~v1_funct_1(X33)|r1_tarski(k9_relat_1(X33,k10_relat_1(X33,X32)),X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 1.21/1.44  cnf(c_0_19, plain, (X2=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|k9_relat_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.21/1.44  cnf(c_0_20, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.21/1.44  cnf(c_0_21, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.21/1.44  cnf(c_0_22, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.21/1.44  fof(c_0_23, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1)))), inference(assume_negation,[status(cth)],[t152_funct_1])).
% 1.21/1.44  cnf(c_0_24, plain, (k10_relat_1(X1,X2)=k1_xboole_0|k9_relat_1(X1,k10_relat_1(X1,X2))!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 1.21/1.44  cnf(c_0_25, plain, (k9_relat_1(X1,k10_relat_1(X1,k1_xboole_0))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 1.21/1.44  fof(c_0_26, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(v2_funct_1(esk3_0)&~r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)),esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 1.21/1.44  fof(c_0_27, plain, ![X29, X30, X31]:(~v1_relat_1(X31)|~v1_funct_1(X31)|(~v2_funct_1(X31)|k9_relat_1(X31,k6_subset_1(X29,X30))=k6_subset_1(k9_relat_1(X31,X29),k9_relat_1(X31,X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).
% 1.21/1.44  fof(c_0_28, plain, ![X20, X21]:k6_subset_1(X20,X21)=k4_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 1.21/1.44  cnf(c_0_29, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 1.21/1.44  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.21/1.44  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.21/1.44  cnf(c_0_32, plain, (k9_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.21/1.44  cnf(c_0_33, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.21/1.44  cnf(c_0_34, negated_conjecture, (k10_relat_1(esk3_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 1.21/1.44  fof(c_0_35, plain, ![X7, X8]:((k4_xboole_0(X7,X8)!=k1_xboole_0|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|k4_xboole_0(X7,X8)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.21/1.44  cnf(c_0_36, plain, (k9_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_33])).
% 1.21/1.44  cnf(c_0_37, negated_conjecture, (k9_relat_1(esk3_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_34]), c_0_30]), c_0_31])])).
% 1.21/1.44  cnf(c_0_38, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.21/1.44  cnf(c_0_39, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.21/1.44  cnf(c_0_40, negated_conjecture, (k4_xboole_0(k9_relat_1(esk3_0,X1),k1_xboole_0)=k9_relat_1(esk3_0,k4_xboole_0(X1,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_30]), c_0_31])])).
% 1.21/1.44  fof(c_0_41, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.21/1.44  cnf(c_0_42, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,X1),k1_xboole_0)|k9_relat_1(esk3_0,k4_xboole_0(X1,k1_xboole_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.21/1.44  cnf(c_0_43, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.21/1.44  fof(c_0_44, plain, ![X16]:r1_tarski(k1_xboole_0,X16), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.21/1.44  fof(c_0_45, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 1.21/1.44  cnf(c_0_46, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.21/1.44  cnf(c_0_47, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,X1),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_37])])).
% 1.21/1.44  cnf(c_0_48, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.21/1.44  cnf(c_0_49, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.21/1.44  cnf(c_0_50, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|k9_relat_1(X1,k4_xboole_0(X2,X3))!=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_36])).
% 1.21/1.44  cnf(c_0_51, negated_conjecture, (k9_relat_1(esk3_0,X1)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 1.21/1.44  fof(c_0_52, plain, ![X34, X35]:(~v1_relat_1(X35)|(~r1_tarski(X34,k1_relat_1(X35))|r1_tarski(X34,k10_relat_1(X35,k9_relat_1(X35,X34))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 1.21/1.44  fof(c_0_53, plain, ![X17, X18]:r1_tarski(k4_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 1.21/1.44  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~v1_funct_1(X3)|~v1_relat_1(X3)|~r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,X2)))), inference(spm,[status(thm)],[c_0_49, c_0_22])).
% 1.21/1.44  cnf(c_0_55, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2))|~r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_38]), c_0_30]), c_0_31])])).
% 1.21/1.44  cnf(c_0_56, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.21/1.44  cnf(c_0_57, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.21/1.44  cnf(c_0_58, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,X1),X2)|~r1_tarski(k4_xboole_0(X1,k10_relat_1(esk3_0,X2)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_30]), c_0_31])])).
% 1.21/1.44  cnf(c_0_59, plain, (r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X3)))|~v1_relat_1(X2)|~r1_tarski(X3,k1_relat_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_49, c_0_56])).
% 1.21/1.44  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_49, c_0_57])).
% 1.21/1.44  cnf(c_0_61, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,X1),X2)|~r1_tarski(X1,k10_relat_1(esk3_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_43]), c_0_48])])).
% 1.21/1.44  cnf(c_0_62, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.21/1.44  cnf(c_0_63, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_48])).
% 1.21/1.44  cnf(c_0_64, plain, (k10_relat_1(X1,k9_relat_1(X1,X2))=X3|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X3)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_46, c_0_59])).
% 1.21/1.44  cnf(c_0_65, plain, (r1_tarski(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k10_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_49, c_0_20])).
% 1.21/1.44  cnf(c_0_66, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,X1),X2)|~r1_tarski(X1,k10_relat_1(esk3_0,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 1.21/1.44  cnf(c_0_67, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_62])).
% 1.21/1.44  cnf(c_0_68, plain, (k4_xboole_0(X1,X2)=X1|~r1_tarski(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_46, c_0_57])).
% 1.21/1.44  cnf(c_0_69, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,X1),X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_63, c_0_47])).
% 1.21/1.44  cnf(c_0_70, negated_conjecture, (k1_xboole_0=X1|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_51]), c_0_34]), c_0_31]), c_0_34]), c_0_48])]), c_0_63])).
% 1.21/1.44  cnf(c_0_71, plain, (r1_tarski(k4_xboole_0(k10_relat_1(X1,X2),X3),k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_57])).
% 1.21/1.44  cnf(c_0_72, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,k4_xboole_0(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 1.21/1.44  cnf(c_0_73, negated_conjecture, (k4_xboole_0(k9_relat_1(esk3_0,X1),X2)=k9_relat_1(esk3_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 1.21/1.44  cnf(c_0_74, negated_conjecture, (k1_xboole_0=X1|~r1_tarski(X1,k9_relat_1(esk3_0,X2))|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_70, c_0_69])).
% 1.21/1.44  cnf(c_0_75, plain, (k4_xboole_0(k10_relat_1(X1,X2),X3)=k1_xboole_0|k9_relat_1(X1,k4_xboole_0(k10_relat_1(X1,X2),X3))!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_71])).
% 1.21/1.44  cnf(c_0_76, negated_conjecture, (k9_relat_1(esk3_0,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0|~r1_tarski(k9_relat_1(esk3_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_40])).
% 1.21/1.44  cnf(c_0_77, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,k9_relat_1(esk3_0,X3))|~r1_tarski(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_69])).
% 1.21/1.44  cnf(c_0_78, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1))),k9_relat_1(esk3_0,X1))|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 1.21/1.44  cnf(c_0_79, negated_conjecture, (k9_relat_1(esk3_0,X1)=k1_xboole_0|~r1_tarski(X1,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X2)))|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_61])).
% 1.21/1.44  cnf(c_0_80, negated_conjecture, (k4_xboole_0(k10_relat_1(esk3_0,X1),k1_xboole_0)=k1_xboole_0|~r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_31])])).
% 1.21/1.44  cnf(c_0_81, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1))),X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 1.21/1.44  cnf(c_0_82, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,k10_relat_1(X2,X3))),k1_relat_1(X2))|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_22])).
% 1.21/1.44  cnf(c_0_83, negated_conjecture, (k9_relat_1(esk3_0,k9_relat_1(esk3_0,X1))=k1_xboole_0|~r1_tarski(X1,k10_relat_1(esk3_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X2))))|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_61])).
% 1.21/1.44  cnf(c_0_84, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,X1),k1_xboole_0)|~r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_80])).
% 1.21/1.44  cnf(c_0_85, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)))=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_81])).
% 1.21/1.44  fof(c_0_86, plain, ![X9, X10, X11]:(((r1_tarski(X9,esk1_3(X9,X10,X11))|(~r1_tarski(X9,X10)|~r1_tarski(X11,X10))|X10=k2_xboole_0(X9,X11))&(r1_tarski(X11,esk1_3(X9,X10,X11))|(~r1_tarski(X9,X10)|~r1_tarski(X11,X10))|X10=k2_xboole_0(X9,X11)))&(~r1_tarski(X10,esk1_3(X9,X10,X11))|(~r1_tarski(X9,X10)|~r1_tarski(X11,X10))|X10=k2_xboole_0(X9,X11))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).
% 1.21/1.44  cnf(c_0_87, plain, (k9_relat_1(X1,k10_relat_1(X1,k10_relat_1(X2,X3)))=k1_xboole_0|k9_relat_1(X2,k9_relat_1(X1,k10_relat_1(X1,k10_relat_1(X2,X3))))!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_82])).
% 1.21/1.44  cnf(c_0_88, negated_conjecture, (k9_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)))))=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_83, c_0_67])).
% 1.21/1.44  cnf(c_0_89, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_48])])).
% 1.21/1.44  cnf(c_0_90, plain, (r1_tarski(X1,esk1_3(X2,X3,X1))|X3=k2_xboole_0(X2,X1)|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 1.21/1.44  cnf(c_0_91, plain, (k9_relat_1(X1,k4_xboole_0(X2,X3))=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_43, c_0_36])).
% 1.21/1.44  cnf(c_0_92, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1))))=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_30]), c_0_31])])).
% 1.21/1.44  cnf(c_0_93, plain, (k10_relat_1(X1,k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)|~r1_tarski(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_46, c_0_56])).
% 1.21/1.44  cnf(c_0_94, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_63, c_0_89])).
% 1.21/1.44  fof(c_0_95, plain, ![X26, X27, X28]:(~v1_relat_1(X28)|k10_relat_1(X28,k2_xboole_0(X26,X27))=k2_xboole_0(k10_relat_1(X28,X26),k10_relat_1(X28,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 1.21/1.44  cnf(c_0_96, plain, (X1=k2_xboole_0(k1_xboole_0,X2)|r1_tarski(X2,esk1_3(k1_xboole_0,X1,X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_90, c_0_48])).
% 1.21/1.44  cnf(c_0_97, plain, (k9_relat_1(X1,k4_xboole_0(X2,X2))=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_91, c_0_67])).
% 1.21/1.44  cnf(c_0_98, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_57])).
% 1.21/1.44  cnf(c_0_99, negated_conjecture, (k10_relat_1(esk3_0,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)))=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_92]), c_0_31])])).
% 1.21/1.44  cnf(c_0_100, negated_conjecture, (k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1))=X1|~r1_tarski(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_31])]), c_0_63])).
% 1.21/1.44  cnf(c_0_101, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 1.21/1.44  cnf(c_0_102, plain, (X1=k2_xboole_0(X2,X3)|~r1_tarski(X1,esk1_3(X2,X1,X3))|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 1.21/1.44  cnf(c_0_103, plain, (k2_xboole_0(k1_xboole_0,X1)=X1|r1_tarski(X1,esk1_3(k1_xboole_0,X1,X1))), inference(spm,[status(thm)],[c_0_96, c_0_67])).
% 1.21/1.44  cnf(c_0_104, negated_conjecture, (k9_relat_1(esk3_0,k4_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_97]), c_0_98]), c_0_38]), c_0_30]), c_0_31])])).
% 1.21/1.44  cnf(c_0_105, negated_conjecture, (k10_relat_1(esk3_0,X1)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 1.21/1.44  cnf(c_0_106, negated_conjecture, (k2_xboole_0(k1_xboole_0,k10_relat_1(esk3_0,X1))=k10_relat_1(esk3_0,k2_xboole_0(k1_xboole_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_34]), c_0_31])])).
% 1.21/1.44  cnf(c_0_107, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_67]), c_0_48])])).
% 1.21/1.44  cnf(c_0_108, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,X1)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_104]), c_0_37]), c_0_38]), c_0_30]), c_0_31])])).
% 1.21/1.44  cnf(c_0_109, negated_conjecture, (k10_relat_1(esk3_0,k2_xboole_0(X1,X2))=k10_relat_1(esk3_0,X2)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_105]), c_0_106]), c_0_107]), c_0_31])])).
% 1.21/1.44  cnf(c_0_110, negated_conjecture, (k9_relat_1(esk3_0,k4_xboole_0(X1,X1))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_108]), c_0_48])])).
% 1.21/1.44  cnf(c_0_111, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0))|~r1_tarski(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_109]), c_0_31])])).
% 1.21/1.44  cnf(c_0_112, negated_conjecture, (k4_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X1))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_110]), c_0_31])])).
% 1.21/1.44  cnf(c_0_113, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_111, c_0_72])).
% 1.21/1.44  cnf(c_0_114, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_112]), c_0_48])])).
% 1.21/1.44  cnf(c_0_115, negated_conjecture, (r1_tarski(X1,k1_relat_1(esk3_0))|~r1_tarski(X1,k10_relat_1(esk3_0,X2))), inference(spm,[status(thm)],[c_0_49, c_0_113])).
% 1.21/1.44  cnf(c_0_116, negated_conjecture, (k9_relat_1(esk3_0,k4_xboole_0(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_114]), c_0_38]), c_0_30]), c_0_31])])).
% 1.21/1.44  cnf(c_0_117, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,X1),X2),k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_115, c_0_57])).
% 1.21/1.44  cnf(c_0_118, negated_conjecture, (k4_xboole_0(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_116]), c_0_34]), c_0_31]), c_0_34]), c_0_48]), c_0_117])])).
% 1.21/1.44  cnf(c_0_119, negated_conjecture, (~r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.21/1.44  cnf(c_0_120, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1)), inference(spm,[status(thm)],[c_0_39, c_0_118])).
% 1.21/1.44  cnf(c_0_121, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_120])]), ['proof']).
% 1.21/1.44  # SZS output end CNFRefutation
% 1.21/1.44  # Proof object total steps             : 122
% 1.21/1.44  # Proof object clause steps            : 91
% 1.21/1.44  # Proof object formula steps           : 31
% 1.21/1.44  # Proof object conjectures             : 53
% 1.21/1.44  # Proof object clause conjectures      : 50
% 1.21/1.44  # Proof object formula conjectures     : 3
% 1.21/1.44  # Proof object initial clauses used    : 21
% 1.21/1.44  # Proof object initial formulas used   : 15
% 1.21/1.44  # Proof object generating inferences   : 67
% 1.21/1.44  # Proof object simplifying inferences  : 82
% 1.21/1.44  # Training examples: 0 positive, 0 negative
% 1.21/1.44  # Parsed axioms                        : 15
% 1.21/1.44  # Removed by relevancy pruning/SinE    : 0
% 1.21/1.44  # Initial clauses                      : 23
% 1.21/1.44  # Removed in clause preprocessing      : 1
% 1.21/1.44  # Initial clauses in saturation        : 22
% 1.21/1.44  # Processed clauses                    : 8273
% 1.21/1.44  # ...of these trivial                  : 30
% 1.21/1.44  # ...subsumed                          : 7220
% 1.21/1.44  # ...remaining for further processing  : 1023
% 1.21/1.44  # Other redundant clauses eliminated   : 3
% 1.21/1.44  # Clauses deleted for lack of memory   : 0
% 1.21/1.44  # Backward-subsumed                    : 91
% 1.21/1.44  # Backward-rewritten                   : 65
% 1.21/1.44  # Generated clauses                    : 106120
% 1.21/1.44  # ...of the previous two non-trivial   : 84856
% 1.21/1.44  # Contextual simplify-reflections      : 10
% 1.21/1.44  # Paramodulations                      : 106117
% 1.21/1.44  # Factorizations                       : 0
% 1.21/1.44  # Equation resolutions                 : 3
% 1.21/1.44  # Propositional unsat checks           : 0
% 1.21/1.44  #    Propositional check models        : 0
% 1.21/1.44  #    Propositional check unsatisfiable : 0
% 1.21/1.44  #    Propositional clauses             : 0
% 1.21/1.44  #    Propositional clauses after purity: 0
% 1.21/1.44  #    Propositional unsat core size     : 0
% 1.21/1.44  #    Propositional preprocessing time  : 0.000
% 1.21/1.44  #    Propositional encoding time       : 0.000
% 1.21/1.44  #    Propositional solver time         : 0.000
% 1.21/1.44  #    Success case prop preproc time    : 0.000
% 1.21/1.44  #    Success case prop encoding time   : 0.000
% 1.21/1.44  #    Success case prop solver time     : 0.000
% 1.21/1.44  # Current number of processed clauses  : 844
% 1.21/1.44  #    Positive orientable unit clauses  : 74
% 1.21/1.44  #    Positive unorientable unit clauses: 0
% 1.21/1.44  #    Negative unit clauses             : 2
% 1.21/1.44  #    Non-unit-clauses                  : 768
% 1.21/1.44  # Current number of unprocessed clauses: 75812
% 1.21/1.44  # ...number of literals in the above   : 280690
% 1.21/1.44  # Current number of archived formulas  : 0
% 1.21/1.44  # Current number of archived clauses   : 178
% 1.21/1.44  # Clause-clause subsumption calls (NU) : 83093
% 1.21/1.44  # Rec. Clause-clause subsumption calls : 63167
% 1.21/1.44  # Non-unit clause-clause subsumptions  : 7307
% 1.21/1.44  # Unit Clause-clause subsumption calls : 1555
% 1.21/1.44  # Rewrite failures with RHS unbound    : 0
% 1.21/1.44  # BW rewrite match attempts            : 751
% 1.21/1.44  # BW rewrite match successes           : 38
% 1.21/1.44  # Condensation attempts                : 0
% 1.21/1.44  # Condensation successes               : 0
% 1.21/1.44  # Termbank termtop insertions          : 2314431
% 1.21/1.44  
% 1.21/1.44  # -------------------------------------------------
% 1.21/1.44  # User time                : 1.021 s
% 1.21/1.44  # System time              : 0.059 s
% 1.21/1.44  # Total time               : 1.080 s
% 1.21/1.44  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
