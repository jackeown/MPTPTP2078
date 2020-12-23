%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:44 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 422 expanded)
%              Number of clauses        :   41 ( 182 expanded)
%              Number of leaves         :   16 ( 108 expanded)
%              Depth                    :   14
%              Number of atoms          :  148 ( 973 expanded)
%              Number of equality atoms :   46 ( 307 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t151_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(t137_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(k1_xboole_0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t117_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k8_relat_1(X1,X2),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(fc9_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(t95_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t144_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_16,plain,(
    ! [X7] : v1_relat_1(k6_relat_1(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k9_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t151_relat_1])).

fof(c_0_18,plain,(
    ! [X18] :
      ( ~ v1_relat_1(X18)
      | k8_relat_1(k1_xboole_0,X18) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t137_relat_1])])).

cnf(c_0_19,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

fof(c_0_21,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | k2_relat_1(k7_relat_1(X23,X22)) = k9_relat_1(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ( k9_relat_1(esk2_0,esk1_0) != k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(esk2_0),esk1_0) )
    & ( k9_relat_1(esk2_0,esk1_0) = k1_xboole_0
      | r1_xboole_0(k1_relat_1(esk2_0),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_23,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | r1_tarski(k8_relat_1(X14,X15),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).

cnf(c_0_24,plain,
    ( k8_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_26,plain,(
    ! [X12] :
      ( v1_xboole_0(X12)
      | ~ v1_relat_1(X12)
      | ~ v1_xboole_0(k2_relat_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).

cnf(c_0_27,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X24,X25] :
      ( ( k7_relat_1(X25,X24) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X25),X24)
        | ~ v1_relat_1(X25) )
      & ( ~ r1_xboole_0(k1_relat_1(X25),X24)
        | k7_relat_1(X25,X24) = k1_xboole_0
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).

fof(c_0_30,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(X5)
      | ~ r1_tarski(X5,X4)
      | ~ r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_31,plain,
    ( r1_tarski(k8_relat_1(X2,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_33,plain,(
    ! [X3] : r1_xboole_0(X3,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk2_0,X1)) = k9_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( k9_relat_1(esk2_0,esk1_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_25])])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(k7_relat_1(esk2_0,X1))
    | ~ v1_relat_1(k7_relat_1(esk2_0,X1))
    | ~ v1_xboole_0(k9_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k9_relat_1(esk2_0,esk1_0) = k1_xboole_0
    | k7_relat_1(esk2_0,esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_28])])).

cnf(c_0_43,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

fof(c_0_44,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | v1_relat_1(k7_relat_1(X8,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_45,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | r1_tarski(k9_relat_1(X20,X19),k2_relat_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).

fof(c_0_46,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | v1_relat_1(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_47,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) = k1_xboole_0
    | v1_xboole_0(k7_relat_1(esk2_0,esk1_0))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_48,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_49,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | k9_relat_1(X21,k1_relat_1(X21)) = k2_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_50,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) = k1_xboole_0
    | v1_xboole_0(k7_relat_1(esk2_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_28])])).

cnf(c_0_53,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_54,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | ~ r1_tarski(k2_relat_1(X17),X16)
      | k8_relat_1(X16,X17) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k9_relat_1(k7_relat_1(esk2_0,X1),X2),k9_relat_1(esk2_0,X1))
    | ~ v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) = k1_xboole_0
    | v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2))) = k2_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_48])).

cnf(c_0_58,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) = k1_xboole_0
    | r1_tarski(k9_relat_1(k7_relat_1(esk2_0,esk1_0),X1),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_42]),c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk2_0,X1),k1_relat_1(k7_relat_1(esk2_0,X1))) = k9_relat_1(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_28]),c_0_35])).

cnf(c_0_61,plain,
    ( k8_relat_1(k1_xboole_0,k7_relat_1(X1,X2)) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_48])).

cnf(c_0_62,negated_conjecture,
    ( k9_relat_1(esk2_0,esk1_0) != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_63,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k7_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_64,negated_conjecture,
    ( k8_relat_1(X1,k7_relat_1(esk2_0,X2)) = k7_relat_1(esk2_0,X2)
    | ~ v1_relat_1(k7_relat_1(esk2_0,X2))
    | ~ r1_tarski(k9_relat_1(esk2_0,X2),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_35])).

cnf(c_0_65,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) = k1_xboole_0
    | r1_tarski(k9_relat_1(esk2_0,esk1_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k8_relat_1(k1_xboole_0,k7_relat_1(esk2_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_28])).

cnf(c_0_67,negated_conjecture,
    ( k9_relat_1(esk2_0,esk1_0) != k1_xboole_0
    | k7_relat_1(esk2_0,esk1_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_28])])).

cnf(c_0_68,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])]),c_0_56])).

cnf(c_0_69,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_70,negated_conjecture,
    ( k9_relat_1(esk2_0,esk1_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_68]),c_0_69]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S04AI
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.39  fof(t151_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 0.13/0.39  fof(t137_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k8_relat_1(k1_xboole_0,X1)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 0.13/0.39  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.13/0.39  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.13/0.39  fof(t117_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k8_relat_1(X1,X2),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 0.13/0.39  fof(fc9_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 0.13/0.39  fof(t95_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 0.13/0.39  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.13/0.39  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.13/0.39  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.13/0.39  fof(t144_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 0.13/0.39  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.13/0.39  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.13/0.39  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 0.13/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.13/0.39  fof(c_0_16, plain, ![X7]:v1_relat_1(k6_relat_1(X7)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.39  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t151_relat_1])).
% 0.13/0.39  fof(c_0_18, plain, ![X18]:(~v1_relat_1(X18)|k8_relat_1(k1_xboole_0,X18)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t137_relat_1])])).
% 0.13/0.39  cnf(c_0_19, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_20, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.13/0.39  fof(c_0_21, plain, ![X22, X23]:(~v1_relat_1(X23)|k2_relat_1(k7_relat_1(X23,X22))=k9_relat_1(X23,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.13/0.39  fof(c_0_22, negated_conjecture, (v1_relat_1(esk2_0)&((k9_relat_1(esk2_0,esk1_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk2_0),esk1_0))&(k9_relat_1(esk2_0,esk1_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk2_0),esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.13/0.39  fof(c_0_23, plain, ![X14, X15]:(~v1_relat_1(X15)|r1_tarski(k8_relat_1(X14,X15),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).
% 0.13/0.39  cnf(c_0_24, plain, (k8_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_25, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.39  fof(c_0_26, plain, ![X12]:(v1_xboole_0(X12)|~v1_relat_1(X12)|~v1_xboole_0(k2_relat_1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).
% 0.13/0.39  cnf(c_0_27, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  fof(c_0_29, plain, ![X24, X25]:((k7_relat_1(X25,X24)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X25),X24)|~v1_relat_1(X25))&(~r1_xboole_0(k1_relat_1(X25),X24)|k7_relat_1(X25,X24)=k1_xboole_0|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).
% 0.13/0.39  fof(c_0_30, plain, ![X4, X5]:(v1_xboole_0(X5)|(~r1_tarski(X5,X4)|~r1_xboole_0(X5,X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.13/0.39  cnf(c_0_31, plain, (r1_tarski(k8_relat_1(X2,X1),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_32, plain, (k8_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.39  fof(c_0_33, plain, ![X3]:r1_xboole_0(X3,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.13/0.39  cnf(c_0_34, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (k2_relat_1(k7_relat_1(esk2_0,X1))=k9_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.39  cnf(c_0_36, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (k9_relat_1(esk2_0,esk1_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_38, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  cnf(c_0_39, plain, (r1_tarski(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_25])])).
% 0.13/0.39  cnf(c_0_40, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (v1_xboole_0(k7_relat_1(esk2_0,X1))|~v1_relat_1(k7_relat_1(esk2_0,X1))|~v1_xboole_0(k9_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (k9_relat_1(esk2_0,esk1_0)=k1_xboole_0|k7_relat_1(esk2_0,esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_28])])).
% 0.13/0.39  cnf(c_0_43, plain, (v1_xboole_0(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.13/0.39  fof(c_0_44, plain, ![X8, X9]:(~v1_relat_1(X8)|v1_relat_1(k7_relat_1(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.13/0.39  fof(c_0_45, plain, ![X19, X20]:(~v1_relat_1(X20)|r1_tarski(k9_relat_1(X20,X19),k2_relat_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).
% 0.13/0.39  fof(c_0_46, plain, ![X6]:(~v1_xboole_0(X6)|v1_relat_1(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)=k1_xboole_0|v1_xboole_0(k7_relat_1(esk2_0,esk1_0))|~v1_relat_1(k7_relat_1(esk2_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.13/0.39  cnf(c_0_48, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.39  fof(c_0_49, plain, ![X21]:(~v1_relat_1(X21)|k9_relat_1(X21,k1_relat_1(X21))=k2_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.13/0.39  cnf(c_0_50, plain, (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.39  cnf(c_0_51, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)=k1_xboole_0|v1_xboole_0(k7_relat_1(esk2_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_28])])).
% 0.13/0.39  cnf(c_0_53, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.39  fof(c_0_54, plain, ![X16, X17]:(~v1_relat_1(X17)|(~r1_tarski(k2_relat_1(X17),X16)|k8_relat_1(X16,X17)=X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (r1_tarski(k9_relat_1(k7_relat_1(esk2_0,X1),X2),k9_relat_1(esk2_0,X1))|~v1_relat_1(k7_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_50, c_0_35])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)=k1_xboole_0|v1_relat_1(k7_relat_1(esk2_0,esk1_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.13/0.39  cnf(c_0_57, plain, (k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2)))=k2_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_48])).
% 0.13/0.39  cnf(c_0_58, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)=k1_xboole_0|r1_tarski(k9_relat_1(k7_relat_1(esk2_0,esk1_0),X1),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_42]), c_0_56])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (k9_relat_1(k7_relat_1(esk2_0,X1),k1_relat_1(k7_relat_1(esk2_0,X1)))=k9_relat_1(esk2_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_28]), c_0_35])).
% 0.13/0.39  cnf(c_0_61, plain, (k8_relat_1(k1_xboole_0,k7_relat_1(X1,X2))=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_48])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (k9_relat_1(esk2_0,esk1_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_63, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k7_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_64, negated_conjecture, (k8_relat_1(X1,k7_relat_1(esk2_0,X2))=k7_relat_1(esk2_0,X2)|~v1_relat_1(k7_relat_1(esk2_0,X2))|~r1_tarski(k9_relat_1(esk2_0,X2),X1)), inference(spm,[status(thm)],[c_0_58, c_0_35])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)=k1_xboole_0|r1_tarski(k9_relat_1(esk2_0,esk1_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (k8_relat_1(k1_xboole_0,k7_relat_1(esk2_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_28])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (k9_relat_1(esk2_0,esk1_0)!=k1_xboole_0|k7_relat_1(esk2_0,esk1_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_28])])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])]), c_0_56])).
% 0.13/0.39  cnf(c_0_69, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.39  cnf(c_0_70, negated_conjecture, (k9_relat_1(esk2_0,esk1_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68])])).
% 0.13/0.39  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_68]), c_0_69]), c_0_70]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 72
% 0.13/0.39  # Proof object clause steps            : 41
% 0.13/0.39  # Proof object formula steps           : 31
% 0.13/0.39  # Proof object conjectures             : 22
% 0.13/0.39  # Proof object clause conjectures      : 19
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 19
% 0.13/0.39  # Proof object initial formulas used   : 16
% 0.13/0.39  # Proof object generating inferences   : 21
% 0.13/0.39  # Proof object simplifying inferences  : 21
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 19
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 24
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 24
% 0.13/0.39  # Processed clauses                    : 212
% 0.13/0.39  # ...of these trivial                  : 11
% 0.13/0.39  # ...subsumed                          : 16
% 0.13/0.39  # ...remaining for further processing  : 184
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 4
% 0.13/0.39  # Backward-rewritten                   : 41
% 0.13/0.39  # Generated clauses                    : 786
% 0.13/0.39  # ...of the previous two non-trivial   : 337
% 0.13/0.39  # Contextual simplify-reflections      : 4
% 0.13/0.39  # Paramodulations                      : 785
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 115
% 0.13/0.39  #    Positive orientable unit clauses  : 67
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 1
% 0.13/0.39  #    Non-unit-clauses                  : 47
% 0.13/0.39  # Current number of unprocessed clauses: 146
% 0.13/0.39  # ...number of literals in the above   : 234
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 69
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 359
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 323
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 22
% 0.13/0.39  # Unit Clause-clause subsumption calls : 110
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 27
% 0.13/0.39  # BW rewrite match successes           : 14
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 9215
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.041 s
% 0.13/0.39  # System time              : 0.003 s
% 0.13/0.39  # Total time               : 0.044 s
% 0.13/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
