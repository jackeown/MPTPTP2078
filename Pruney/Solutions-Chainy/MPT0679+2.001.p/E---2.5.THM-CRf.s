%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:26 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 381 expanded)
%              Number of clauses        :   49 ( 163 expanded)
%              Number of leaves         :   14 ( 103 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 615 expanded)
%              Number of equality atoms :   49 ( 329 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t123_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t121_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

fof(t149_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(t155_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)),k9_relat_1(X3,k6_subset_1(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_14,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_tarski(X25,X26)
      | ~ r1_xboole_0(X25,X27)
      | r1_tarski(X25,k4_xboole_0(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

fof(c_0_15,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_17,plain,(
    ! [X16] : k3_xboole_0(X16,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_18,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_19,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k3_xboole_0(X19,X20)) = k4_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( v2_funct_1(X3)
         => k9_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t123_funct_1])).

fof(c_0_21,plain,(
    ! [X23,X24] : r1_xboole_0(k4_xboole_0(X23,X24),X24) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_27,plain,(
    ! [X17,X18] : r1_tarski(k4_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X34,X35,X36] :
      ( ~ v1_relat_1(X36)
      | ~ v1_funct_1(X36)
      | ~ v2_funct_1(X36)
      | k9_relat_1(X36,k3_xboole_0(X34,X35)) = k3_xboole_0(k9_relat_1(X36,X34),k9_relat_1(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_1])])).

fof(c_0_31,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & v2_funct_1(esk4_0)
    & k9_relat_1(esk4_0,k6_subset_1(esk2_0,esk3_0)) != k6_subset_1(k9_relat_1(esk4_0,esk2_0),k9_relat_1(esk4_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_32,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_33,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | k9_relat_1(X30,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_23]),c_0_23])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_23]),c_0_23])).

cnf(c_0_40,plain,
    ( k9_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_23])).

cnf(c_0_46,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k1_xboole_0))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_25])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_23])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_38]),c_0_39])).

fof(c_0_51,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_relat_1(X33)
      | r1_tarski(k6_subset_1(k9_relat_1(X33,X31),k9_relat_1(X33,X32)),k9_relat_1(X33,k6_subset_1(X31,X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_relat_1])])).

fof(c_0_52,plain,(
    ! [X28,X29] : k6_subset_1(X28,X29) = k4_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_53,negated_conjecture,
    ( k9_relat_1(esk4_0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(esk4_0,X1),k9_relat_1(esk4_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])])).

cnf(c_0_54,plain,
    ( k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k9_relat_1(esk4_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_43])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_25])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_50])).

cnf(c_0_60,plain,
    ( r1_tarski(k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3)),k9_relat_1(X1,k6_subset_1(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_45])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k9_relat_1(esk4_0,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_65,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(k9_relat_1(esk4_0,X1),k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_50])).

cnf(c_0_67,plain,
    ( r1_tarski(k5_xboole_0(k9_relat_1(X1,X2),k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))),k9_relat_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_61]),c_0_23]),c_0_23])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_38])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k5_xboole_0(X3,k3_xboole_0(X3,k9_relat_1(esk4_0,X2))))
    | ~ r1_tarski(k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k9_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( r1_tarski(k5_xboole_0(k9_relat_1(X1,X2),k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,k3_xboole_0(X2,X3)))),k9_relat_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( k9_relat_1(esk4_0,k6_subset_1(esk2_0,esk3_0)) != k6_subset_1(k9_relat_1(esk4_0,esk2_0),k9_relat_1(esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k5_xboole_0(k9_relat_1(esk4_0,X1),k3_xboole_0(k9_relat_1(esk4_0,X1),k9_relat_1(esk4_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k9_relat_1(esk4_0,X1),k3_xboole_0(k9_relat_1(esk4_0,X1),k9_relat_1(esk4_0,X2))),k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_53]),c_0_68]),c_0_43])])).

cnf(c_0_75,negated_conjecture,
    ( k9_relat_1(esk4_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) != k5_xboole_0(k9_relat_1(esk4_0,esk2_0),k3_xboole_0(k9_relat_1(esk4_0,esk2_0),k9_relat_1(esk4_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_61]),c_0_61]),c_0_23]),c_0_23])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(k9_relat_1(esk4_0,X1),k3_xboole_0(k9_relat_1(esk4_0,X1),k9_relat_1(esk4_0,X2))) = k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_73]),c_0_74])])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.46/0.64  # AutoSched0-Mode selected heuristic G_E___024_B31_F1_PI_AE_Q4_CS_SP_S2S
% 0.46/0.64  # and selection function SelectNewComplexAHP.
% 0.46/0.64  #
% 0.46/0.64  # Preprocessing time       : 0.026 s
% 0.46/0.64  
% 0.46/0.64  # Proof found!
% 0.46/0.64  # SZS status Theorem
% 0.46/0.64  # SZS output start CNFRefutation
% 0.46/0.64  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.46/0.64  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.46/0.64  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.46/0.64  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.46/0.64  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.46/0.64  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.46/0.64  fof(t123_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 0.46/0.64  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.46/0.64  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.46/0.64  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.46/0.64  fof(t121_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 0.46/0.64  fof(t149_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_relat_1)).
% 0.46/0.64  fof(t155_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2)),k9_relat_1(X3,k6_subset_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_relat_1)).
% 0.46/0.64  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.46/0.64  fof(c_0_14, plain, ![X25, X26, X27]:(~r1_tarski(X25,X26)|~r1_xboole_0(X25,X27)|r1_tarski(X25,k4_xboole_0(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 0.46/0.64  fof(c_0_15, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.46/0.64  fof(c_0_16, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.46/0.64  fof(c_0_17, plain, ![X16]:k3_xboole_0(X16,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.46/0.64  fof(c_0_18, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.46/0.64  fof(c_0_19, plain, ![X19, X20]:k4_xboole_0(X19,k3_xboole_0(X19,X20))=k4_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.46/0.64  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t123_funct_1])).
% 0.46/0.64  fof(c_0_21, plain, ![X23, X24]:r1_xboole_0(k4_xboole_0(X23,X24),X24), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.46/0.64  cnf(c_0_22, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.46/0.64  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.64  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.46/0.64  cnf(c_0_25, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.46/0.64  fof(c_0_26, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.46/0.64  fof(c_0_27, plain, ![X17, X18]:r1_tarski(k4_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.46/0.64  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.64  cnf(c_0_29, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.64  fof(c_0_30, plain, ![X34, X35, X36]:(~v1_relat_1(X36)|~v1_funct_1(X36)|(~v2_funct_1(X36)|k9_relat_1(X36,k3_xboole_0(X34,X35))=k3_xboole_0(k9_relat_1(X36,X34),k9_relat_1(X36,X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_1])])).
% 0.46/0.64  fof(c_0_31, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(v2_funct_1(esk4_0)&k9_relat_1(esk4_0,k6_subset_1(esk2_0,esk3_0))!=k6_subset_1(k9_relat_1(esk4_0,esk2_0),k9_relat_1(esk4_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.46/0.64  cnf(c_0_32, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.46/0.64  fof(c_0_33, plain, ![X30]:(~v1_relat_1(X30)|k9_relat_1(X30,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).
% 0.46/0.64  cnf(c_0_34, plain, (r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.46/0.64  cnf(c_0_35, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.46/0.64  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.46/0.64  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.46/0.64  cnf(c_0_38, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_23]), c_0_23])).
% 0.46/0.64  cnf(c_0_39, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_23]), c_0_23])).
% 0.46/0.64  cnf(c_0_40, plain, (k9_relat_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.46/0.64  cnf(c_0_41, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.46/0.64  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.46/0.64  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.46/0.64  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.46/0.64  cnf(c_0_45, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_32, c_0_23])).
% 0.46/0.64  cnf(c_0_46, plain, (k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.46/0.64  cnf(c_0_47, plain, (r1_tarski(X1,k5_xboole_0(X2,k1_xboole_0))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_25])).
% 0.46/0.64  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36])).
% 0.46/0.64  cnf(c_0_49, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_37, c_0_23])).
% 0.46/0.64  cnf(c_0_50, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_38]), c_0_39])).
% 0.46/0.64  fof(c_0_51, plain, ![X31, X32, X33]:(~v1_relat_1(X33)|r1_tarski(k6_subset_1(k9_relat_1(X33,X31),k9_relat_1(X33,X32)),k9_relat_1(X33,k6_subset_1(X31,X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_relat_1])])).
% 0.46/0.64  fof(c_0_52, plain, ![X28, X29]:k6_subset_1(X28,X29)=k4_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.46/0.64  cnf(c_0_53, negated_conjecture, (k9_relat_1(esk4_0,k3_xboole_0(X1,X2))=k3_xboole_0(k9_relat_1(esk4_0,X1),k9_relat_1(esk4_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43])])).
% 0.46/0.64  cnf(c_0_54, plain, (k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.46/0.64  cnf(c_0_55, negated_conjecture, (k9_relat_1(esk4_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_43])).
% 0.46/0.64  cnf(c_0_56, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.46/0.64  cnf(c_0_57, plain, (r1_tarski(X1,k5_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.46/0.64  cnf(c_0_58, plain, (r1_tarski(k5_xboole_0(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_49, c_0_25])).
% 0.46/0.64  cnf(c_0_59, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_38, c_0_50])).
% 0.46/0.64  cnf(c_0_60, plain, (r1_tarski(k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3)),k9_relat_1(X1,k6_subset_1(X2,X3)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.46/0.64  cnf(c_0_61, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.46/0.64  cnf(c_0_62, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_34, c_0_45])).
% 0.46/0.64  cnf(c_0_63, negated_conjecture, (k3_xboole_0(k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k9_relat_1(esk4_0,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.46/0.64  cnf(c_0_64, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.46/0.64  cnf(c_0_65, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_59])).
% 0.46/0.64  cnf(c_0_66, negated_conjecture, (k3_xboole_0(k9_relat_1(esk4_0,X1),k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_53, c_0_50])).
% 0.46/0.64  cnf(c_0_67, plain, (r1_tarski(k5_xboole_0(k9_relat_1(X1,X2),k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))),k9_relat_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_61]), c_0_23]), c_0_23])).
% 0.46/0.64  cnf(c_0_68, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_38])).
% 0.46/0.64  cnf(c_0_69, negated_conjecture, (r1_tarski(k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k5_xboole_0(X3,k3_xboole_0(X3,k9_relat_1(esk4_0,X2))))|~r1_tarski(k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_64])).
% 0.46/0.64  cnf(c_0_70, negated_conjecture, (r1_tarski(k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k9_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.46/0.64  cnf(c_0_71, plain, (r1_tarski(k5_xboole_0(k9_relat_1(X1,X2),k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,k3_xboole_0(X2,X3)))),k9_relat_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.46/0.64  cnf(c_0_72, negated_conjecture, (k9_relat_1(esk4_0,k6_subset_1(esk2_0,esk3_0))!=k6_subset_1(k9_relat_1(esk4_0,esk2_0),k9_relat_1(esk4_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.46/0.64  cnf(c_0_73, negated_conjecture, (r1_tarski(k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k5_xboole_0(k9_relat_1(esk4_0,X1),k3_xboole_0(k9_relat_1(esk4_0,X1),k9_relat_1(esk4_0,X2))))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.46/0.64  cnf(c_0_74, negated_conjecture, (r1_tarski(k5_xboole_0(k9_relat_1(esk4_0,X1),k3_xboole_0(k9_relat_1(esk4_0,X1),k9_relat_1(esk4_0,X2))),k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_53]), c_0_68]), c_0_43])])).
% 0.46/0.64  cnf(c_0_75, negated_conjecture, (k9_relat_1(esk4_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))!=k5_xboole_0(k9_relat_1(esk4_0,esk2_0),k3_xboole_0(k9_relat_1(esk4_0,esk2_0),k9_relat_1(esk4_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_61]), c_0_61]), c_0_23]), c_0_23])).
% 0.46/0.64  cnf(c_0_76, negated_conjecture, (k5_xboole_0(k9_relat_1(esk4_0,X1),k3_xboole_0(k9_relat_1(esk4_0,X1),k9_relat_1(esk4_0,X2)))=k9_relat_1(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_73]), c_0_74])])).
% 0.46/0.64  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])]), ['proof']).
% 0.46/0.64  # SZS output end CNFRefutation
% 0.46/0.64  # Proof object total steps             : 78
% 0.46/0.64  # Proof object clause steps            : 49
% 0.46/0.64  # Proof object formula steps           : 29
% 0.46/0.64  # Proof object conjectures             : 18
% 0.46/0.64  # Proof object clause conjectures      : 15
% 0.46/0.64  # Proof object formula conjectures     : 3
% 0.46/0.64  # Proof object initial clauses used    : 19
% 0.46/0.64  # Proof object initial formulas used   : 14
% 0.46/0.64  # Proof object generating inferences   : 20
% 0.46/0.64  # Proof object simplifying inferences  : 36
% 0.46/0.64  # Training examples: 0 positive, 0 negative
% 0.46/0.64  # Parsed axioms                        : 15
% 0.46/0.64  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.64  # Initial clauses                      : 22
% 0.46/0.64  # Removed in clause preprocessing      : 2
% 0.46/0.64  # Initial clauses in saturation        : 20
% 0.46/0.64  # Processed clauses                    : 1239
% 0.46/0.64  # ...of these trivial                  : 375
% 0.46/0.64  # ...subsumed                          : 585
% 0.46/0.64  # ...remaining for further processing  : 279
% 0.46/0.64  # Other redundant clauses eliminated   : 2
% 0.46/0.64  # Clauses deleted for lack of memory   : 0
% 0.46/0.64  # Backward-subsumed                    : 2
% 0.46/0.64  # Backward-rewritten                   : 49
% 0.46/0.64  # Generated clauses                    : 26014
% 0.46/0.64  # ...of the previous two non-trivial   : 15336
% 0.46/0.64  # Contextual simplify-reflections      : 1
% 0.46/0.64  # Paramodulations                      : 26011
% 0.46/0.64  # Factorizations                       : 0
% 0.46/0.64  # Equation resolutions                 : 3
% 0.46/0.64  # Propositional unsat checks           : 0
% 0.46/0.64  #    Propositional check models        : 0
% 0.46/0.64  #    Propositional check unsatisfiable : 0
% 0.46/0.64  #    Propositional clauses             : 0
% 0.46/0.64  #    Propositional clauses after purity: 0
% 0.46/0.64  #    Propositional unsat core size     : 0
% 0.46/0.64  #    Propositional preprocessing time  : 0.000
% 0.46/0.64  #    Propositional encoding time       : 0.000
% 0.46/0.64  #    Propositional solver time         : 0.000
% 0.46/0.64  #    Success case prop preproc time    : 0.000
% 0.46/0.64  #    Success case prop encoding time   : 0.000
% 0.46/0.64  #    Success case prop solver time     : 0.000
% 0.46/0.64  # Current number of processed clauses  : 226
% 0.46/0.64  #    Positive orientable unit clauses  : 96
% 0.46/0.64  #    Positive unorientable unit clauses: 0
% 0.46/0.64  #    Negative unit clauses             : 1
% 0.46/0.64  #    Non-unit-clauses                  : 129
% 0.46/0.64  # Current number of unprocessed clauses: 13623
% 0.46/0.64  # ...number of literals in the above   : 50486
% 0.46/0.64  # Current number of archived formulas  : 0
% 0.46/0.64  # Current number of archived clauses   : 53
% 0.46/0.64  # Clause-clause subsumption calls (NU) : 3526
% 0.46/0.64  # Rec. Clause-clause subsumption calls : 1272
% 0.46/0.64  # Non-unit clause-clause subsumptions  : 461
% 0.46/0.64  # Unit Clause-clause subsumption calls : 52
% 0.46/0.64  # Rewrite failures with RHS unbound    : 0
% 0.46/0.64  # BW rewrite match attempts            : 230
% 0.46/0.64  # BW rewrite match successes           : 19
% 0.46/0.64  # Condensation attempts                : 0
% 0.46/0.64  # Condensation successes               : 0
% 0.46/0.64  # Termbank termtop insertions          : 934520
% 0.46/0.65  
% 0.46/0.65  # -------------------------------------------------
% 0.46/0.65  # User time                : 0.289 s
% 0.46/0.65  # System time              : 0.015 s
% 0.46/0.65  # Total time               : 0.305 s
% 0.46/0.65  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
