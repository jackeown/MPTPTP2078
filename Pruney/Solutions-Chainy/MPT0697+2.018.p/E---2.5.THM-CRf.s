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
% DateTime   : Thu Dec  3 10:55:04 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 481 expanded)
%              Number of clauses        :   67 ( 221 expanded)
%              Number of leaves         :   12 ( 120 expanded)
%              Depth                    :   23
%              Number of atoms          :  257 (1263 expanded)
%              Number of equality atoms :   47 ( 320 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

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

fof(t123_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_12,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_13,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_16,plain,(
    ! [X11,X12] : r1_tarski(k4_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_17,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | k10_relat_1(X23,k6_subset_1(X21,X22)) = k6_subset_1(k10_relat_1(X23,X21),k10_relat_1(X23,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

fof(c_0_18,plain,(
    ! [X14,X15] : k6_subset_1(X14,X15) = k4_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_19,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | r1_tarski(k10_relat_1(X17,X16),k1_relat_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_20,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ r1_tarski(X26,k1_relat_1(X27))
      | r1_tarski(X26,k10_relat_1(X27,k9_relat_1(X27,X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | r1_tarski(k9_relat_1(X25,k10_relat_1(X25,X24)),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k1_relat_1(X1) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_22])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t152_funct_1])).

fof(c_0_38,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_relat_1(X20)
      | ~ v1_funct_1(X20)
      | ~ v2_funct_1(X20)
      | k9_relat_1(X20,k6_subset_1(X18,X19)) = k6_subset_1(k9_relat_1(X20,X18),k9_relat_1(X20,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_31])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k10_relat_1(X2,X3))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k10_relat_1(X2,k4_xboole_0(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,k4_xboole_0(X2,X3))),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_34])).

cnf(c_0_42,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1))) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_44,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v2_funct_1(esk2_0)
    & ~ r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).

cnf(c_0_45,plain,
    ( k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_39])).

fof(c_0_47,plain,(
    ! [X13] : k4_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k10_relat_1(X2,X3))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k10_relat_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_31])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,k4_xboole_0(X2,X4)))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_41])).

cnf(c_0_50,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))) = k4_xboole_0(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_42])).

cnf(c_0_51,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | k10_relat_1(X1,k4_xboole_0(X2,X3)) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_33])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k9_relat_1(X1,k10_relat_1(X1,X2)),X2) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_34])).

cnf(c_0_53,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_33]),c_0_31])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_26]),c_0_26])).

cnf(c_0_57,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,k1_xboole_0)) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_34])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( r1_tarski(k10_relat_1(X1,k1_xboole_0),k10_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_22])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k9_relat_1(X3,k4_xboole_0(k10_relat_1(X3,X2),k1_relat_1(X3)))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k10_relat_1(X1,X2),k1_relat_1(X1)) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_29])).

cnf(c_0_62,plain,
    ( r1_tarski(k10_relat_1(X1,k9_relat_1(X2,k10_relat_1(X2,X3))),k10_relat_1(X1,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_64,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,k10_relat_1(X1,k1_xboole_0))) = k9_relat_1(X1,X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k10_relat_1(X1,k1_xboole_0),k10_relat_1(X1,X2)) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_59])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k9_relat_1(X3,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k9_relat_1(X1,k10_relat_1(X1,k1_xboole_0))),k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_54]),c_0_55])])).

cnf(c_0_68,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,k1_xboole_0)) = k9_relat_1(X1,k1_xboole_0)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,plain,
    ( r1_tarski(k9_relat_1(X1,k1_xboole_0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_22])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_39])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k9_relat_1(X1,k1_xboole_0)),k1_xboole_0)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,plain,
    ( X1 = k9_relat_1(X2,k1_xboole_0)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k9_relat_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k9_relat_1(X1,k1_xboole_0)),X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k9_relat_1(X2,k1_xboole_0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k9_relat_1(X1,k1_xboole_0)),X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(X1,k1_xboole_0)) = k1_xboole_0
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_75])).

cnf(c_0_77,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_78,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(X1,k1_xboole_0)) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_54]),c_0_55])])).

cnf(c_0_79,negated_conjecture,
    ( k10_relat_1(esk2_0,k4_xboole_0(X1,k9_relat_1(X2,k1_xboole_0))) = k10_relat_1(esk2_0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_78]),c_0_58]),c_0_54]),c_0_55])])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k10_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_29])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_79]),c_0_54]),c_0_55])])).

cnf(c_0_82,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(X1,X2),X3),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_24])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1) = k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_81])).

cnf(c_0_84,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(X1,X2),X3),k10_relat_1(X1,k9_relat_1(X1,k4_xboole_0(k10_relat_1(X1,X2),X3))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( k9_relat_1(esk2_0,k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)) = k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_83]),c_0_77]),c_0_54]),c_0_55])])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1),k1_xboole_0)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_63]),c_0_55])])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1) = k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_86]),c_0_58])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_54]),c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.65  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4c
% 0.19/0.65  # and selection function SelectCQPrecWNTNp.
% 0.19/0.65  #
% 0.19/0.65  # Preprocessing time       : 0.027 s
% 0.19/0.65  # Presaturation interreduction done
% 0.19/0.65  
% 0.19/0.65  # Proof found!
% 0.19/0.65  # SZS status Theorem
% 0.19/0.65  # SZS output start CNFRefutation
% 0.19/0.65  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.65  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.65  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.65  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.65  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 0.19/0.65  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.19/0.65  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.19/0.65  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 0.19/0.65  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.19/0.65  fof(t152_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 0.19/0.65  fof(t123_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 0.19/0.65  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.65  fof(c_0_12, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.65  fof(c_0_13, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.65  cnf(c_0_14, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.65  fof(c_0_15, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X9,X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.65  fof(c_0_16, plain, ![X11, X12]:r1_tarski(k4_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.65  fof(c_0_17, plain, ![X21, X22, X23]:(~v1_relat_1(X23)|~v1_funct_1(X23)|k10_relat_1(X23,k6_subset_1(X21,X22))=k6_subset_1(k10_relat_1(X23,X21),k10_relat_1(X23,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 0.19/0.65  fof(c_0_18, plain, ![X14, X15]:k6_subset_1(X14,X15)=k4_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.19/0.65  fof(c_0_19, plain, ![X16, X17]:(~v1_relat_1(X17)|r1_tarski(k10_relat_1(X17,X16),k1_relat_1(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.19/0.65  fof(c_0_20, plain, ![X26, X27]:(~v1_relat_1(X27)|(~r1_tarski(X26,k1_relat_1(X27))|r1_tarski(X26,k10_relat_1(X27,k9_relat_1(X27,X26))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.19/0.65  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.65  cnf(c_0_22, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_14])).
% 0.19/0.65  cnf(c_0_23, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.65  cnf(c_0_24, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.65  cnf(c_0_25, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.65  cnf(c_0_26, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.65  fof(c_0_27, plain, ![X24, X25]:(~v1_relat_1(X25)|~v1_funct_1(X25)|r1_tarski(k9_relat_1(X25,k10_relat_1(X25,X24)),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.19/0.65  cnf(c_0_28, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.65  cnf(c_0_29, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.65  cnf(c_0_30, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.65  cnf(c_0_31, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.65  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.65  cnf(c_0_33, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_26])).
% 0.19/0.65  cnf(c_0_34, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.65  cnf(c_0_35, plain, (k1_relat_1(X1)=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.65  cnf(c_0_36, plain, (r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_22])).
% 0.19/0.65  fof(c_0_37, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1)))), inference(assume_negation,[status(cth)],[t152_funct_1])).
% 0.19/0.65  fof(c_0_38, plain, ![X18, X19, X20]:(~v1_relat_1(X20)|~v1_funct_1(X20)|(~v2_funct_1(X20)|k9_relat_1(X20,k6_subset_1(X18,X19))=k6_subset_1(k9_relat_1(X20,X18),k9_relat_1(X20,X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).
% 0.19/0.65  cnf(c_0_39, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_31])).
% 0.19/0.65  cnf(c_0_40, plain, (r1_tarski(X1,k10_relat_1(X2,X3))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r1_tarski(X1,k10_relat_1(X2,k4_xboole_0(X3,X4)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.65  cnf(c_0_41, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,k4_xboole_0(X2,X3))),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_34])).
% 0.19/0.65  cnf(c_0_42, plain, (k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1)))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.65  cnf(c_0_43, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.65  fof(c_0_44, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(v2_funct_1(esk2_0)&~r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).
% 0.19/0.65  cnf(c_0_45, plain, (k9_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.65  cnf(c_0_46, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_39])).
% 0.19/0.65  fof(c_0_47, plain, ![X13]:k4_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.65  cnf(c_0_48, plain, (r1_tarski(X1,k10_relat_1(X2,X3))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r1_tarski(X1,k10_relat_1(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_40, c_0_31])).
% 0.19/0.65  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~v1_funct_1(X3)|~v1_relat_1(X3)|~r1_tarski(X1,k9_relat_1(X3,k10_relat_1(X3,k4_xboole_0(X2,X4))))), inference(spm,[status(thm)],[c_0_23, c_0_41])).
% 0.19/0.65  cnf(c_0_50, plain, (k10_relat_1(X1,k4_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1))))=k4_xboole_0(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_42])).
% 0.19/0.65  cnf(c_0_51, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|k10_relat_1(X1,k4_xboole_0(X2,X3))!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_33])).
% 0.19/0.65  cnf(c_0_52, plain, (k4_xboole_0(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_34])).
% 0.19/0.65  cnf(c_0_53, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_33]), c_0_31])).
% 0.19/0.65  cnf(c_0_54, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.65  cnf(c_0_55, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.65  cnf(c_0_56, plain, (k9_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_26]), c_0_26])).
% 0.19/0.65  cnf(c_0_57, plain, (k9_relat_1(X1,k10_relat_1(X1,k1_xboole_0))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_34])).
% 0.19/0.65  cnf(c_0_58, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.65  cnf(c_0_59, plain, (r1_tarski(k10_relat_1(X1,k1_xboole_0),k10_relat_1(X1,X2))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_22])).
% 0.19/0.65  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~v1_funct_1(X3)|~v1_relat_1(X3)|~r1_tarski(X1,k9_relat_1(X3,k4_xboole_0(k10_relat_1(X3,X2),k1_relat_1(X3))))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.65  cnf(c_0_61, plain, (k4_xboole_0(k10_relat_1(X1,X2),k1_relat_1(X1))=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_29])).
% 0.19/0.65  cnf(c_0_62, plain, (r1_tarski(k10_relat_1(X1,k9_relat_1(X2,k10_relat_1(X2,X3))),k10_relat_1(X1,X3))|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.19/0.65  cnf(c_0_63, negated_conjecture, (k10_relat_1(esk2_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.19/0.65  cnf(c_0_64, plain, (k9_relat_1(X1,k4_xboole_0(X2,k10_relat_1(X1,k1_xboole_0)))=k9_relat_1(X1,X2)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.19/0.65  cnf(c_0_65, plain, (k4_xboole_0(k10_relat_1(X1,k1_xboole_0),k10_relat_1(X1,X2))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_59])).
% 0.19/0.65  cnf(c_0_66, plain, (r1_tarski(X1,X2)|~v1_funct_1(X3)|~v1_relat_1(X3)|~r1_tarski(X1,k9_relat_1(X3,k1_xboole_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.65  cnf(c_0_67, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k9_relat_1(X1,k10_relat_1(X1,k1_xboole_0))),k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_54]), c_0_55])])).
% 0.19/0.65  cnf(c_0_68, plain, (k9_relat_1(X1,k10_relat_1(X1,k1_xboole_0))=k9_relat_1(X1,k1_xboole_0)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.65  cnf(c_0_69, plain, (r1_tarski(k9_relat_1(X1,k1_xboole_0),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_22])).
% 0.19/0.65  cnf(c_0_70, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_39])).
% 0.19/0.65  cnf(c_0_71, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k9_relat_1(X1,k1_xboole_0)),k1_xboole_0)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.65  cnf(c_0_72, plain, (X1=k9_relat_1(X2,k1_xboole_0)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r1_tarski(X1,k9_relat_1(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_28, c_0_69])).
% 0.19/0.65  cnf(c_0_73, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k9_relat_1(X1,k1_xboole_0)),X2)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.65  cnf(c_0_74, plain, (k9_relat_1(X1,k1_xboole_0)=k9_relat_1(X2,k1_xboole_0)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_72, c_0_69])).
% 0.19/0.65  cnf(c_0_75, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k9_relat_1(X1,k1_xboole_0)),X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.65  cnf(c_0_76, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(X1,k1_xboole_0))=k1_xboole_0|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_75])).
% 0.19/0.65  cnf(c_0_77, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.65  cnf(c_0_78, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(X1,k1_xboole_0))=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_54]), c_0_55])])).
% 0.19/0.65  cnf(c_0_79, negated_conjecture, (k10_relat_1(esk2_0,k4_xboole_0(X1,k9_relat_1(X2,k1_xboole_0)))=k10_relat_1(esk2_0,X1)|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_78]), c_0_58]), c_0_54]), c_0_55])])).
% 0.19/0.65  cnf(c_0_80, plain, (r1_tarski(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k10_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_23, c_0_29])).
% 0.19/0.65  cnf(c_0_81, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1)|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_79]), c_0_54]), c_0_55])])).
% 0.19/0.65  cnf(c_0_82, plain, (r1_tarski(k4_xboole_0(k10_relat_1(X1,X2),X3),k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_80, c_0_24])).
% 0.19/0.65  cnf(c_0_83, negated_conjecture, (k4_xboole_0(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1)=k1_xboole_0|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_21, c_0_81])).
% 0.19/0.65  cnf(c_0_84, plain, (r1_tarski(k4_xboole_0(k10_relat_1(X1,X2),X3),k10_relat_1(X1,k9_relat_1(X1,k4_xboole_0(k10_relat_1(X1,X2),X3))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_82])).
% 0.19/0.65  cnf(c_0_85, negated_conjecture, (k9_relat_1(esk2_0,k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1))=k1_xboole_0|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_83]), c_0_77]), c_0_54]), c_0_55])])).
% 0.19/0.65  cnf(c_0_86, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1),k1_xboole_0)|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_63]), c_0_55])])).
% 0.19/0.65  cnf(c_0_87, negated_conjecture, (k4_xboole_0(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)=k1_xboole_0|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_86]), c_0_58])).
% 0.19/0.65  cnf(c_0_88, negated_conjecture, (~r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.65  cnf(c_0_89, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)),X1)|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_43, c_0_87])).
% 0.19/0.65  cnf(c_0_90, negated_conjecture, (~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.19/0.65  cnf(c_0_91, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_54]), c_0_55])]), ['proof']).
% 0.19/0.65  # SZS output end CNFRefutation
% 0.19/0.65  # Proof object total steps             : 92
% 0.19/0.65  # Proof object clause steps            : 67
% 0.19/0.65  # Proof object formula steps           : 25
% 0.19/0.65  # Proof object conjectures             : 23
% 0.19/0.65  # Proof object clause conjectures      : 20
% 0.19/0.65  # Proof object formula conjectures     : 3
% 0.19/0.65  # Proof object initial clauses used    : 17
% 0.19/0.65  # Proof object initial formulas used   : 12
% 0.19/0.65  # Proof object generating inferences   : 47
% 0.19/0.65  # Proof object simplifying inferences  : 33
% 0.19/0.65  # Training examples: 0 positive, 0 negative
% 0.19/0.65  # Parsed axioms                        : 12
% 0.19/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.65  # Initial clauses                      : 18
% 0.19/0.65  # Removed in clause preprocessing      : 1
% 0.19/0.65  # Initial clauses in saturation        : 17
% 0.19/0.65  # Processed clauses                    : 3083
% 0.19/0.65  # ...of these trivial                  : 7
% 0.19/0.65  # ...subsumed                          : 2644
% 0.19/0.65  # ...remaining for further processing  : 432
% 0.19/0.65  # Other redundant clauses eliminated   : 3
% 0.19/0.65  # Clauses deleted for lack of memory   : 0
% 0.19/0.65  # Backward-subsumed                    : 334
% 0.19/0.65  # Backward-rewritten                   : 1
% 0.19/0.65  # Generated clauses                    : 18974
% 0.19/0.65  # ...of the previous two non-trivial   : 16292
% 0.19/0.65  # Contextual simplify-reflections      : 6
% 0.19/0.65  # Paramodulations                      : 18971
% 0.19/0.65  # Factorizations                       : 0
% 0.19/0.65  # Equation resolutions                 : 3
% 0.19/0.65  # Propositional unsat checks           : 0
% 0.19/0.65  #    Propositional check models        : 0
% 0.19/0.65  #    Propositional check unsatisfiable : 0
% 0.19/0.65  #    Propositional clauses             : 0
% 0.19/0.65  #    Propositional clauses after purity: 0
% 0.19/0.65  #    Propositional unsat core size     : 0
% 0.19/0.65  #    Propositional preprocessing time  : 0.000
% 0.19/0.65  #    Propositional encoding time       : 0.000
% 0.19/0.65  #    Propositional solver time         : 0.000
% 0.19/0.65  #    Success case prop preproc time    : 0.000
% 0.19/0.65  #    Success case prop encoding time   : 0.000
% 0.19/0.65  #    Success case prop solver time     : 0.000
% 0.19/0.65  # Current number of processed clauses  : 79
% 0.19/0.65  #    Positive orientable unit clauses  : 19
% 0.19/0.65  #    Positive unorientable unit clauses: 0
% 0.19/0.65  #    Negative unit clauses             : 1
% 0.19/0.65  #    Non-unit-clauses                  : 59
% 0.19/0.65  # Current number of unprocessed clauses: 13126
% 0.19/0.65  # ...number of literals in the above   : 72580
% 0.19/0.65  # Current number of archived formulas  : 0
% 0.19/0.65  # Current number of archived clauses   : 352
% 0.19/0.65  # Clause-clause subsumption calls (NU) : 30003
% 0.19/0.65  # Rec. Clause-clause subsumption calls : 11217
% 0.19/0.65  # Non-unit clause-clause subsumptions  : 2984
% 0.19/0.65  # Unit Clause-clause subsumption calls : 4
% 0.19/0.65  # Rewrite failures with RHS unbound    : 0
% 0.19/0.65  # BW rewrite match attempts            : 62
% 0.19/0.65  # BW rewrite match successes           : 1
% 0.19/0.65  # Condensation attempts                : 0
% 0.19/0.65  # Condensation successes               : 0
% 0.19/0.65  # Termbank termtop insertions          : 361555
% 0.19/0.65  
% 0.19/0.65  # -------------------------------------------------
% 0.19/0.65  # User time                : 0.295 s
% 0.19/0.65  # System time              : 0.010 s
% 0.19/0.65  # Total time               : 0.305 s
% 0.19/0.65  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
