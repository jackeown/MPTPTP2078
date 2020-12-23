%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:05 EST 2020

% Result     : Theorem 1.42s
% Output     : CNFRefutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 238 expanded)
%              Number of clauses        :   42 ( 103 expanded)
%              Number of leaves         :   14 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  141 ( 471 expanded)
%              Number of equality atoms :   30 ( 112 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t152_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t178_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

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

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

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

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t152_funct_1])).

fof(c_0_15,plain,(
    ! [X15,X16] : r1_tarski(k4_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_16,plain,(
    ! [X17] : k4_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_17,plain,(
    ! [X33,X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ r1_tarski(X33,X34)
      | r1_tarski(k10_relat_1(X35,X33),k10_relat_1(X35,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v2_funct_1(esk3_0)
    & ~ r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_19,plain,(
    ! [X42,X43] :
      ( ~ v1_relat_1(X43)
      | ~ v1_funct_1(X43)
      | r1_tarski(k9_relat_1(X43,k10_relat_1(X43,X42)),X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_20,plain,(
    ! [X44,X45] :
      ( ~ v1_relat_1(X45)
      | ~ r1_tarski(X44,k1_relat_1(X45))
      | r1_tarski(X44,k10_relat_1(X45,k9_relat_1(X45,X44))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

fof(c_0_21,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | r1_tarski(k10_relat_1(X32,X31),k1_relat_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_22,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(k4_xboole_0(X22,X23),X24)
      | r1_tarski(X22,k2_xboole_0(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_29,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | X26 = k2_xboole_0(X25,k4_xboole_0(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

fof(c_0_30,plain,(
    ! [X5,X6] :
      ( ( k4_xboole_0(X5,X6) != k1_xboole_0
        | r1_tarski(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | k4_xboole_0(X5,X6) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_31,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_33,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_34,plain,(
    ! [X36,X37,X38] :
      ( ~ v1_relat_1(X38)
      | ~ v1_funct_1(X38)
      | ~ v2_funct_1(X38)
      | k9_relat_1(X38,k6_subset_1(X36,X37)) = k6_subset_1(k9_relat_1(X38,X36),k9_relat_1(X38,X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).

fof(c_0_35,plain,(
    ! [X29,X30] : k6_subset_1(X29,X30) = k4_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_36,plain,(
    ! [X39,X40,X41] :
      ( ~ v1_relat_1(X41)
      | ~ v1_funct_1(X41)
      | k10_relat_1(X41,k6_subset_1(X39,X40)) = k6_subset_1(k10_relat_1(X41,X39),k10_relat_1(X41,X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_26])])).

cnf(c_0_41,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)))
    | ~ r1_tarski(X1,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_26])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))),k10_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_51,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_41,c_0_23])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_23])).

cnf(c_0_55,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_57,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_47]),c_0_47])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X1,X2)),X1)) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))),k10_relat_1(esk3_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_50])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_24]),c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,X1),X2),k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_44])).

cnf(c_0_63,negated_conjecture,
    ( k9_relat_1(esk3_0,k4_xboole_0(X1,X2)) = k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_28]),c_0_26])])).

cnf(c_0_64,negated_conjecture,
    ( k10_relat_1(esk3_0,k4_xboole_0(X1,X2)) = k4_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_28]),c_0_26])])).

cnf(c_0_65,negated_conjecture,
    ( k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))) = k10_relat_1(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61]),c_0_60]),c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,X1),X2),k4_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k9_relat_1(esk3_0,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_62]),c_0_63]),c_0_64]),c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_52])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_67]),c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:23:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.42/1.60  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 1.42/1.60  # and selection function SelectNegativeLiterals.
% 1.42/1.60  #
% 1.42/1.60  # Preprocessing time       : 0.028 s
% 1.42/1.60  # Presaturation interreduction done
% 1.42/1.60  
% 1.42/1.60  # Proof found!
% 1.42/1.60  # SZS status Theorem
% 1.42/1.60  # SZS output start CNFRefutation
% 1.42/1.60  fof(t152_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 1.42/1.60  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.42/1.60  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.42/1.60  fof(t178_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 1.42/1.60  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 1.42/1.60  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 1.42/1.60  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 1.42/1.60  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.42/1.60  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.42/1.60  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.42/1.60  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.42/1.60  fof(t123_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 1.42/1.60  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.42/1.60  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 1.42/1.60  fof(c_0_14, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1)))), inference(assume_negation,[status(cth)],[t152_funct_1])).
% 1.42/1.60  fof(c_0_15, plain, ![X15, X16]:r1_tarski(k4_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 1.42/1.60  fof(c_0_16, plain, ![X17]:k4_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.42/1.60  fof(c_0_17, plain, ![X33, X34, X35]:(~v1_relat_1(X35)|(~r1_tarski(X33,X34)|r1_tarski(k10_relat_1(X35,X33),k10_relat_1(X35,X34)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).
% 1.42/1.60  fof(c_0_18, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(v2_funct_1(esk3_0)&~r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)),esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 1.42/1.60  fof(c_0_19, plain, ![X42, X43]:(~v1_relat_1(X43)|~v1_funct_1(X43)|r1_tarski(k9_relat_1(X43,k10_relat_1(X43,X42)),X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 1.42/1.60  fof(c_0_20, plain, ![X44, X45]:(~v1_relat_1(X45)|(~r1_tarski(X44,k1_relat_1(X45))|r1_tarski(X44,k10_relat_1(X45,k9_relat_1(X45,X44))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 1.42/1.60  fof(c_0_21, plain, ![X31, X32]:(~v1_relat_1(X32)|r1_tarski(k10_relat_1(X32,X31),k1_relat_1(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 1.42/1.60  fof(c_0_22, plain, ![X22, X23, X24]:(~r1_tarski(k4_xboole_0(X22,X23),X24)|r1_tarski(X22,k2_xboole_0(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 1.42/1.60  cnf(c_0_23, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.42/1.60  cnf(c_0_24, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.42/1.60  cnf(c_0_25, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.42/1.60  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.42/1.60  cnf(c_0_27, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.42/1.60  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.42/1.60  fof(c_0_29, plain, ![X25, X26]:(~r1_tarski(X25,X26)|X26=k2_xboole_0(X25,k4_xboole_0(X26,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 1.42/1.60  fof(c_0_30, plain, ![X5, X6]:((k4_xboole_0(X5,X6)!=k1_xboole_0|r1_tarski(X5,X6))&(~r1_tarski(X5,X6)|k4_xboole_0(X5,X6)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.42/1.60  cnf(c_0_31, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.42/1.60  cnf(c_0_32, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.42/1.60  fof(c_0_33, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X12,X13)|r1_tarski(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 1.42/1.60  fof(c_0_34, plain, ![X36, X37, X38]:(~v1_relat_1(X38)|~v1_funct_1(X38)|(~v2_funct_1(X38)|k9_relat_1(X38,k6_subset_1(X36,X37))=k6_subset_1(k9_relat_1(X38,X36),k9_relat_1(X38,X37)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_funct_1])])).
% 1.42/1.60  fof(c_0_35, plain, ![X29, X30]:k6_subset_1(X29,X30)=k4_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 1.42/1.60  fof(c_0_36, plain, ![X39, X40, X41]:(~v1_relat_1(X41)|~v1_funct_1(X41)|k10_relat_1(X41,k6_subset_1(X39,X40))=k6_subset_1(k10_relat_1(X41,X39),k10_relat_1(X41,X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 1.42/1.60  cnf(c_0_37, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.42/1.60  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.42/1.60  cnf(c_0_39, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.42/1.60  cnf(c_0_40, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_26])])).
% 1.42/1.60  cnf(c_0_41, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.42/1.60  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.42/1.60  cnf(c_0_43, negated_conjecture, (r1_tarski(X1,k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)))|~r1_tarski(X1,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_31, c_0_26])).
% 1.42/1.60  cnf(c_0_44, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_26])).
% 1.42/1.60  cnf(c_0_45, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.42/1.60  cnf(c_0_46, plain, (k9_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.42/1.60  cnf(c_0_47, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.42/1.60  cnf(c_0_48, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.42/1.60  cnf(c_0_49, plain, (r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.42/1.60  cnf(c_0_50, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))),k10_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.42/1.60  cnf(c_0_51, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(spm,[status(thm)],[c_0_41, c_0_23])).
% 1.42/1.60  cnf(c_0_52, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_38])).
% 1.42/1.60  cnf(c_0_53, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 1.42/1.60  cnf(c_0_54, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_45, c_0_23])).
% 1.42/1.60  cnf(c_0_55, plain, (k9_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47])).
% 1.42/1.60  cnf(c_0_56, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.42/1.60  cnf(c_0_57, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_47]), c_0_47])).
% 1.42/1.60  cnf(c_0_58, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X1,X2)),X1))=k2_xboole_0(X2,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_41, c_0_49])).
% 1.42/1.60  cnf(c_0_59, negated_conjecture, (k4_xboole_0(k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))),k10_relat_1(esk3_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_50])).
% 1.42/1.60  cnf(c_0_60, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_24]), c_0_52])).
% 1.42/1.60  cnf(c_0_61, negated_conjecture, (k4_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_53])).
% 1.42/1.60  cnf(c_0_62, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,X1),X2),k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_54, c_0_44])).
% 1.42/1.60  cnf(c_0_63, negated_conjecture, (k9_relat_1(esk3_0,k4_xboole_0(X1,X2))=k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_28]), c_0_26])])).
% 1.42/1.60  cnf(c_0_64, negated_conjecture, (k10_relat_1(esk3_0,k4_xboole_0(X1,X2))=k4_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_28]), c_0_26])])).
% 1.42/1.60  cnf(c_0_65, negated_conjecture, (k10_relat_1(esk3_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)))=k10_relat_1(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61]), c_0_60]), c_0_60])).
% 1.42/1.60  cnf(c_0_66, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,X1),X2),k4_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,k9_relat_1(esk3_0,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_62]), c_0_63]), c_0_64]), c_0_65])).
% 1.42/1.60  cnf(c_0_67, negated_conjecture, (r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_66, c_0_52])).
% 1.42/1.60  cnf(c_0_68, negated_conjecture, (~r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.42/1.60  cnf(c_0_69, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,k9_relat_1(esk3_0,X1)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_67]), c_0_60])).
% 1.42/1.60  cnf(c_0_70, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69])]), ['proof']).
% 1.42/1.60  # SZS output end CNFRefutation
% 1.42/1.60  # Proof object total steps             : 71
% 1.42/1.60  # Proof object clause steps            : 42
% 1.42/1.60  # Proof object formula steps           : 29
% 1.42/1.60  # Proof object conjectures             : 23
% 1.42/1.60  # Proof object clause conjectures      : 20
% 1.42/1.60  # Proof object formula conjectures     : 3
% 1.42/1.60  # Proof object initial clauses used    : 17
% 1.42/1.60  # Proof object initial formulas used   : 14
% 1.42/1.60  # Proof object generating inferences   : 22
% 1.42/1.60  # Proof object simplifying inferences  : 22
% 1.42/1.60  # Training examples: 0 positive, 0 negative
% 1.42/1.60  # Parsed axioms                        : 19
% 1.42/1.60  # Removed by relevancy pruning/SinE    : 0
% 1.42/1.60  # Initial clauses                      : 25
% 1.42/1.60  # Removed in clause preprocessing      : 1
% 1.42/1.60  # Initial clauses in saturation        : 24
% 1.42/1.60  # Processed clauses                    : 3723
% 1.42/1.60  # ...of these trivial                  : 831
% 1.42/1.60  # ...subsumed                          : 1839
% 1.42/1.60  # ...remaining for further processing  : 1053
% 1.42/1.60  # Other redundant clauses eliminated   : 0
% 1.42/1.60  # Clauses deleted for lack of memory   : 0
% 1.42/1.60  # Backward-subsumed                    : 3
% 1.42/1.60  # Backward-rewritten                   : 53
% 1.42/1.60  # Generated clauses                    : 164980
% 1.42/1.60  # ...of the previous two non-trivial   : 122666
% 1.42/1.60  # Contextual simplify-reflections      : 0
% 1.42/1.60  # Paramodulations                      : 164979
% 1.42/1.60  # Factorizations                       : 0
% 1.42/1.60  # Equation resolutions                 : 1
% 1.42/1.60  # Propositional unsat checks           : 0
% 1.42/1.60  #    Propositional check models        : 0
% 1.42/1.60  #    Propositional check unsatisfiable : 0
% 1.42/1.60  #    Propositional clauses             : 0
% 1.42/1.60  #    Propositional clauses after purity: 0
% 1.42/1.60  #    Propositional unsat core size     : 0
% 1.42/1.60  #    Propositional preprocessing time  : 0.000
% 1.42/1.60  #    Propositional encoding time       : 0.000
% 1.42/1.60  #    Propositional solver time         : 0.000
% 1.42/1.60  #    Success case prop preproc time    : 0.000
% 1.42/1.60  #    Success case prop encoding time   : 0.000
% 1.42/1.60  #    Success case prop solver time     : 0.000
% 1.42/1.60  # Current number of processed clauses  : 973
% 1.42/1.60  #    Positive orientable unit clauses  : 409
% 1.42/1.60  #    Positive unorientable unit clauses: 0
% 1.42/1.60  #    Negative unit clauses             : 0
% 1.42/1.60  #    Non-unit-clauses                  : 564
% 1.42/1.60  # Current number of unprocessed clauses: 118613
% 1.42/1.60  # ...number of literals in the above   : 254062
% 1.42/1.60  # Current number of archived formulas  : 0
% 1.42/1.60  # Current number of archived clauses   : 81
% 1.42/1.60  # Clause-clause subsumption calls (NU) : 65318
% 1.42/1.60  # Rec. Clause-clause subsumption calls : 25605
% 1.42/1.60  # Non-unit clause-clause subsumptions  : 1842
% 1.42/1.60  # Unit Clause-clause subsumption calls : 6729
% 1.42/1.60  # Rewrite failures with RHS unbound    : 0
% 1.42/1.60  # BW rewrite match attempts            : 3105
% 1.42/1.60  # BW rewrite match successes           : 22
% 1.42/1.60  # Condensation attempts                : 0
% 1.42/1.60  # Condensation successes               : 0
% 1.42/1.60  # Termbank termtop insertions          : 3292199
% 1.42/1.60  
% 1.42/1.60  # -------------------------------------------------
% 1.42/1.60  # User time                : 1.201 s
% 1.42/1.60  # System time              : 0.060 s
% 1.42/1.60  # Total time               : 1.261 s
% 1.42/1.60  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
