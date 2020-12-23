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
% DateTime   : Thu Dec  3 10:54:26 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 356 expanded)
%              Number of clauses        :   50 ( 167 expanded)
%              Number of leaves         :   13 (  90 expanded)
%              Depth                    :   15
%              Number of atoms          :  139 ( 654 expanded)
%              Number of equality atoms :   46 ( 279 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t90_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t75_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t121_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(t123_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t149_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(t155_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)),k9_relat_1(X3,k6_subset_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_13,plain,(
    ! [X26,X27] : r1_xboole_0(k4_xboole_0(X26,k3_xboole_0(X26,X27)),X27) ),
    inference(variable_rename,[status(thm)],[t90_xboole_1])).

fof(c_0_14,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k3_xboole_0(X16,X17)) = k4_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_16,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_17,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

fof(c_0_24,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_25,plain,(
    ! [X21,X22] :
      ( r1_xboole_0(X21,X22)
      | ~ r1_xboole_0(k3_xboole_0(X21,X22),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_28,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_29,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_xboole_0(X23,X25)
      | r1_tarski(X23,k4_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X1,X2))
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_18])).

cnf(c_0_37,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_38,plain,(
    ! [X34,X35,X36] :
      ( ~ v1_relat_1(X36)
      | ~ v1_funct_1(X36)
      | ~ v2_funct_1(X36)
      | k9_relat_1(X36,k3_xboole_0(X34,X35)) = k3_xboole_0(k9_relat_1(X36,X34),k9_relat_1(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_1])])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( v2_funct_1(X3)
         => k9_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t123_funct_1])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_42,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_43,plain,
    ( k9_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v2_funct_1(esk3_0)
    & k9_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0)) != k6_subset_1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_48,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | k9_relat_1(X30,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).

fof(c_0_49,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_relat_1(X33)
      | r1_tarski(k6_subset_1(k9_relat_1(X33,X31),k9_relat_1(X33,X32)),k9_relat_1(X33,k6_subset_1(X31,X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_relat_1])])).

fof(c_0_50,plain,(
    ! [X28,X29] : k6_subset_1(X28,X29) = k4_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_51,plain,
    ( k9_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k9_relat_1(X1,X2),k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_18]),c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_28])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_57,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( r1_tarski(k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3)),k9_relat_1(X1,k6_subset_1(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( k9_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k9_relat_1(esk3_0,X1),k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_55]),c_0_47])])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_56]),c_0_56]),c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_54])).

cnf(c_0_64,plain,
    ( r1_tarski(k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3)),k9_relat_1(X1,k4_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_59])).

cnf(c_0_65,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_47])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(k9_relat_1(esk3_0,X1),k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,k4_xboole_0(X1,X2)))) = k9_relat_1(esk3_0,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_23])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(k9_relat_1(esk3_0,k4_xboole_0(X1,X2)),k4_xboole_0(k9_relat_1(esk3_0,k4_xboole_0(X1,X2)),k9_relat_1(esk3_0,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2)),k9_relat_1(esk3_0,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_54])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,X2)),k4_xboole_0(k9_relat_1(esk3_0,X1),X3))
    | ~ r1_xboole_0(k9_relat_1(esk3_0,k4_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(k9_relat_1(esk3_0,k4_xboole_0(X1,X2)),k9_relat_1(esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( k9_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0)) != k6_subset_1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_72,negated_conjecture,
    ( k9_relat_1(esk3_0,k4_xboole_0(X1,X2)) = k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2))
    | ~ r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,X2)),k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,X2)),k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( k9_relat_1(esk3_0,k4_xboole_0(esk1_0,esk2_0)) != k4_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_59]),c_0_59])).

cnf(c_0_75,negated_conjecture,
    ( k9_relat_1(esk3_0,k4_xboole_0(X1,X2)) = k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 0.20/0.45  # and selection function SelectComplexG.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.027 s
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(t90_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 0.20/0.45  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.45  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.20/0.45  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.45  fof(t75_xboole_1, axiom, ![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 0.20/0.45  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.20/0.45  fof(t121_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 0.20/0.45  fof(t123_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 0.20/0.45  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.45  fof(t149_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 0.20/0.45  fof(t155_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)),k9_relat_1(X3,k6_subset_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_relat_1)).
% 0.20/0.45  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.20/0.45  fof(c_0_13, plain, ![X26, X27]:r1_xboole_0(k4_xboole_0(X26,k3_xboole_0(X26,X27)),X27), inference(variable_rename,[status(thm)],[t90_xboole_1])).
% 0.20/0.45  fof(c_0_14, plain, ![X18, X19]:k4_xboole_0(X18,k4_xboole_0(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.45  fof(c_0_15, plain, ![X16, X17]:k4_xboole_0(X16,k3_xboole_0(X16,X17))=k4_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.20/0.45  fof(c_0_16, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.45  cnf(c_0_17, plain, (r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.45  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.45  cnf(c_0_19, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.45  cnf(c_0_20, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.45  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.45  cnf(c_0_22, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.45  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.20/0.45  fof(c_0_24, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.45  fof(c_0_25, plain, ![X21, X22]:(r1_xboole_0(X21,X22)|~r1_xboole_0(k3_xboole_0(X21,X22),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).
% 0.20/0.45  cnf(c_0_26, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_20, c_0_18])).
% 0.20/0.45  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_18])).
% 0.20/0.45  cnf(c_0_28, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.45  fof(c_0_29, plain, ![X23, X24, X25]:(~r1_tarski(X23,X24)|~r1_xboole_0(X23,X25)|r1_tarski(X23,k4_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 0.20/0.45  cnf(c_0_30, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.45  cnf(c_0_31, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k3_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.45  cnf(c_0_32, plain, (r1_xboole_0(X1,k4_xboole_0(X1,X2))|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_23])).
% 0.20/0.45  cnf(c_0_33, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.45  cnf(c_0_34, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.45  cnf(c_0_35, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_30])).
% 0.20/0.45  cnf(c_0_36, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_31, c_0_18])).
% 0.20/0.45  cnf(c_0_37, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.45  fof(c_0_38, plain, ![X34, X35, X36]:(~v1_relat_1(X36)|~v1_funct_1(X36)|(~v2_funct_1(X36)|k9_relat_1(X36,k3_xboole_0(X34,X35))=k3_xboole_0(k9_relat_1(X36,X34),k9_relat_1(X36,X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_1])])).
% 0.20/0.45  fof(c_0_39, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t123_funct_1])).
% 0.20/0.45  cnf(c_0_40, plain, (r1_tarski(X1,k4_xboole_0(X1,X2))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.45  cnf(c_0_41, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.45  fof(c_0_42, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.45  cnf(c_0_43, plain, (k9_relat_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.45  fof(c_0_44, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(v2_funct_1(esk3_0)&k9_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0))!=k6_subset_1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 0.20/0.45  cnf(c_0_45, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.45  cnf(c_0_46, plain, (r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.45  cnf(c_0_47, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.45  fof(c_0_48, plain, ![X30]:(~v1_relat_1(X30)|k9_relat_1(X30,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).
% 0.20/0.45  fof(c_0_49, plain, ![X31, X32, X33]:(~v1_relat_1(X33)|r1_tarski(k6_subset_1(k9_relat_1(X33,X31),k9_relat_1(X33,X32)),k9_relat_1(X33,k6_subset_1(X31,X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_relat_1])])).
% 0.20/0.45  fof(c_0_50, plain, ![X28, X29]:k6_subset_1(X28,X29)=k4_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.20/0.45  cnf(c_0_51, plain, (k9_relat_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k4_xboole_0(k9_relat_1(X1,X2),k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3)))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_18]), c_0_18])).
% 0.20/0.45  cnf(c_0_52, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.45  cnf(c_0_53, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.45  cnf(c_0_54, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.45  cnf(c_0_55, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X2))), inference(spm,[status(thm)],[c_0_40, c_0_28])).
% 0.20/0.45  cnf(c_0_56, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.20/0.45  cnf(c_0_57, plain, (k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.45  cnf(c_0_58, plain, (r1_tarski(k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3)),k9_relat_1(X1,k6_subset_1(X2,X3)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.45  cnf(c_0_59, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.45  cnf(c_0_60, negated_conjecture, (k9_relat_1(esk3_0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(k9_relat_1(esk3_0,X1),k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])])).
% 0.20/0.45  cnf(c_0_61, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_55]), c_0_47])])).
% 0.20/0.45  cnf(c_0_62, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_56]), c_0_56]), c_0_56])).
% 0.20/0.45  cnf(c_0_63, negated_conjecture, (k9_relat_1(esk3_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_54])).
% 0.20/0.45  cnf(c_0_64, plain, (r1_tarski(k4_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3)),k9_relat_1(X1,k4_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_59])).
% 0.20/0.45  cnf(c_0_65, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))|~r1_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_34, c_0_47])).
% 0.20/0.45  cnf(c_0_66, negated_conjecture, (k4_xboole_0(k9_relat_1(esk3_0,X1),k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,k4_xboole_0(X1,X2))))=k9_relat_1(esk3_0,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_60, c_0_23])).
% 0.20/0.45  cnf(c_0_67, negated_conjecture, (k4_xboole_0(k9_relat_1(esk3_0,k4_xboole_0(X1,X2)),k4_xboole_0(k9_relat_1(esk3_0,k4_xboole_0(X1,X2)),k9_relat_1(esk3_0,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_63])).
% 0.20/0.45  cnf(c_0_68, negated_conjecture, (r1_tarski(k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2)),k9_relat_1(esk3_0,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_64, c_0_54])).
% 0.20/0.45  cnf(c_0_69, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,X2)),k4_xboole_0(k9_relat_1(esk3_0,X1),X3))|~r1_xboole_0(k9_relat_1(esk3_0,k4_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.45  cnf(c_0_70, negated_conjecture, (r1_xboole_0(k9_relat_1(esk3_0,k4_xboole_0(X1,X2)),k9_relat_1(esk3_0,X2))), inference(spm,[status(thm)],[c_0_26, c_0_67])).
% 0.20/0.45  cnf(c_0_71, negated_conjecture, (k9_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0))!=k6_subset_1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.45  cnf(c_0_72, negated_conjecture, (k9_relat_1(esk3_0,k4_xboole_0(X1,X2))=k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2))|~r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,X2)),k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_45, c_0_68])).
% 0.20/0.45  cnf(c_0_73, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k4_xboole_0(X1,X2)),k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.45  cnf(c_0_74, negated_conjecture, (k9_relat_1(esk3_0,k4_xboole_0(esk1_0,esk2_0))!=k4_xboole_0(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_59]), c_0_59])).
% 0.20/0.45  cnf(c_0_75, negated_conjecture, (k9_relat_1(esk3_0,k4_xboole_0(X1,X2))=k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])])).
% 0.20/0.45  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75])]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 77
% 0.20/0.45  # Proof object clause steps            : 50
% 0.20/0.45  # Proof object formula steps           : 27
% 0.20/0.45  # Proof object conjectures             : 19
% 0.20/0.45  # Proof object clause conjectures      : 16
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 18
% 0.20/0.45  # Proof object initial formulas used   : 13
% 0.20/0.45  # Proof object generating inferences   : 20
% 0.20/0.45  # Proof object simplifying inferences  : 28
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 16
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 23
% 0.20/0.45  # Removed in clause preprocessing      : 2
% 0.20/0.45  # Initial clauses in saturation        : 21
% 0.20/0.45  # Processed clauses                    : 1031
% 0.20/0.45  # ...of these trivial                  : 58
% 0.20/0.45  # ...subsumed                          : 794
% 0.20/0.45  # ...remaining for further processing  : 179
% 0.20/0.45  # Other redundant clauses eliminated   : 2
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 2
% 0.20/0.45  # Backward-rewritten                   : 99
% 0.20/0.45  # Generated clauses                    : 7963
% 0.20/0.45  # ...of the previous two non-trivial   : 3073
% 0.20/0.45  # Contextual simplify-reflections      : 0
% 0.20/0.45  # Paramodulations                      : 7960
% 0.20/0.45  # Factorizations                       : 0
% 0.20/0.45  # Equation resolutions                 : 3
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 76
% 0.20/0.45  #    Positive orientable unit clauses  : 41
% 0.20/0.45  #    Positive unorientable unit clauses: 0
% 0.20/0.45  #    Negative unit clauses             : 0
% 0.20/0.45  #    Non-unit-clauses                  : 35
% 0.20/0.45  # Current number of unprocessed clauses: 1960
% 0.20/0.45  # ...number of literals in the above   : 2825
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 103
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 2585
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 2584
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 796
% 0.20/0.45  # Unit Clause-clause subsumption calls : 35
% 0.20/0.45  # Rewrite failures with RHS unbound    : 0
% 0.20/0.45  # BW rewrite match attempts            : 168
% 0.20/0.45  # BW rewrite match successes           : 24
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 143102
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.101 s
% 0.20/0.45  # System time              : 0.006 s
% 0.20/0.45  # Total time               : 0.107 s
% 0.20/0.45  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
