%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   91 (3475 expanded)
%              Number of clauses        :   63 (1667 expanded)
%              Number of leaves         :   14 ( 925 expanded)
%              Depth                    :   23
%              Number of atoms          :  196 (6556 expanded)
%              Number of equality atoms :   52 (1524 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(t44_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc9_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(involutiveness_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k4_relat_1(k4_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(c_0_14,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(X3)
      | X3 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_15,plain,(
    v1_xboole_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | r1_tarski(k1_relat_1(k5_relat_1(X15,X16)),k1_relat_1(X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).

cnf(c_0_17,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_21,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_22,plain,
    ( esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X1)),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_22])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X1)),k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

fof(c_0_27,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X1)),k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

fof(c_0_29,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X12] :
      ( v1_xboole_0(X12)
      | ~ v1_relat_1(X12)
      | ~ v1_xboole_0(k2_relat_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).

fof(c_0_34,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | v1_relat_1(k4_relat_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

cnf(c_0_35,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

fof(c_0_36,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | v1_relat_1(k5_relat_1(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_39,plain,(
    ! [X14] :
      ( ( k2_relat_1(X14) = k1_relat_1(k4_relat_1(X14))
        | ~ v1_relat_1(X14) )
      & ( k1_relat_1(X14) = k2_relat_1(k4_relat_1(X14))
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),X1)),k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_35])).

cnf(c_0_41,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( v1_xboole_0(k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(k4_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),X1)),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_45,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | k4_relat_1(k4_relat_1(X13)) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

cnf(c_0_46,plain,
    ( v1_xboole_0(k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),X1)),k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_24]),c_0_25])])).

cnf(c_0_48,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,plain,
    ( k4_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_46])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),X1)),k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_24])).

cnf(c_0_51,plain,
    ( k4_relat_1(k1_xboole_0) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_49])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_25])).

cnf(c_0_54,plain,
    ( k4_relat_1(k1_xboole_0) = k5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_35]),c_0_25])])).

cnf(c_0_55,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_35]),c_0_25])])).

fof(c_0_56,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_57,plain,
    ( k1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_53]),c_0_32])])).

cnf(c_0_58,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_54]),c_0_20]),c_0_25])]),c_0_55])).

fof(c_0_59,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ( k5_relat_1(k1_xboole_0,esk2_0) != k1_xboole_0
      | k5_relat_1(esk2_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).

cnf(c_0_60,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_57]),c_0_25])])).

cnf(c_0_61,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_41])).

cnf(c_0_62,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_63,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | k4_relat_1(k5_relat_1(X17,X18)) = k5_relat_1(k4_relat_1(X18),k4_relat_1(X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

cnf(c_0_64,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_24])).

cnf(c_0_65,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_24]),c_0_25])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,esk2_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_62])).

cnf(c_0_67,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_20]),c_0_25])])).

cnf(c_0_69,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_65]),c_0_25])])).

cnf(c_0_70,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,esk2_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_66]),c_0_32])])).

cnf(c_0_71,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_72,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(X1),k4_relat_1(X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_67]),c_0_41])).

cnf(c_0_73,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])])).

cnf(c_0_74,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk2_0) = k4_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_70]),c_0_25])])).

cnf(c_0_75,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(X1),k4_relat_1(X2))) = k2_relat_1(k5_relat_1(X2,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_67]),c_0_41])).

cnf(c_0_76,plain,
    ( k1_xboole_0 = X1
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(k4_relat_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_38])).

cnf(c_0_77,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(X1),k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_69])])).

cnf(c_0_78,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk2_0) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_73])).

cnf(c_0_79,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k1_relat_1(k4_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_75]),c_0_38]),c_0_38])).

cnf(c_0_80,plain,
    ( k1_xboole_0 = X1
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_71])).

cnf(c_0_81,plain,
    ( v1_relat_1(k5_relat_1(X1,k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_48]),c_0_38])).

cnf(c_0_82,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk2_0) != k1_xboole_0
    | k5_relat_1(esk2_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_83,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_41]),c_0_62]),c_0_69])])).

cnf(c_0_84,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_69]),c_0_73]),c_0_20])).

cnf(c_0_85,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(k5_relat_1(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( k5_relat_1(esk2_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83])])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k2_relat_1(k5_relat_1(esk2_0,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_62])).

cnf(c_0_88,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(k5_relat_1(esk2_0,k1_xboole_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_62]),c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk2_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_87]),c_0_32])])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:17:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S04CN
% 0.19/0.45  # and selection function MSelectComplexExceptUniqMaxHorn.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.027 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.45  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.19/0.45  fof(t44_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 0.19/0.45  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.19/0.45  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.19/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.45  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.45  fof(fc9_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 0.19/0.45  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.19/0.45  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.19/0.45  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 0.19/0.45  fof(involutiveness_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k4_relat_1(k4_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 0.19/0.45  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 0.19/0.45  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 0.19/0.45  fof(c_0_14, plain, ![X3]:(~v1_xboole_0(X3)|X3=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.45  fof(c_0_15, plain, v1_xboole_0(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.19/0.45  fof(c_0_16, plain, ![X15, X16]:(~v1_relat_1(X15)|(~v1_relat_1(X16)|r1_tarski(k1_relat_1(k5_relat_1(X15,X16)),k1_relat_1(X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).
% 0.19/0.45  cnf(c_0_17, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.45  cnf(c_0_18, plain, (v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.45  cnf(c_0_19, plain, (r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.45  cnf(c_0_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.19/0.45  fof(c_0_21, plain, ![X8]:(~v1_xboole_0(X8)|v1_relat_1(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.19/0.45  cnf(c_0_22, plain, (esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.45  cnf(c_0_23, plain, (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X1)),k1_xboole_0)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.45  cnf(c_0_24, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.45  cnf(c_0_25, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_18, c_0_22])).
% 0.19/0.45  cnf(c_0_26, plain, (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X1)),k1_xboole_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.19/0.45  fof(c_0_27, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.45  cnf(c_0_28, plain, (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X1)),k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.19/0.45  fof(c_0_29, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.45  cnf(c_0_30, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.45  cnf(c_0_31, plain, (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_25])).
% 0.19/0.45  cnf(c_0_32, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.45  fof(c_0_33, plain, ![X12]:(v1_xboole_0(X12)|~v1_relat_1(X12)|~v1_xboole_0(k2_relat_1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).
% 0.19/0.45  fof(c_0_34, plain, ![X9]:(~v1_relat_1(X9)|v1_relat_1(k4_relat_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.19/0.45  cnf(c_0_35, plain, (k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.19/0.45  fof(c_0_36, plain, ![X10, X11]:(~v1_relat_1(X10)|~v1_relat_1(X11)|v1_relat_1(k5_relat_1(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.19/0.45  cnf(c_0_37, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.45  cnf(c_0_38, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.45  fof(c_0_39, plain, ![X14]:((k2_relat_1(X14)=k1_relat_1(k4_relat_1(X14))|~v1_relat_1(X14))&(k1_relat_1(X14)=k2_relat_1(k4_relat_1(X14))|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.19/0.45  cnf(c_0_40, plain, (r1_tarski(k1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),X1)),k1_xboole_0)|~v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_35])).
% 0.19/0.45  cnf(c_0_41, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.45  cnf(c_0_42, plain, (v1_xboole_0(k4_relat_1(X1))|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(k4_relat_1(X1)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.45  cnf(c_0_43, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.45  cnf(c_0_44, plain, (r1_tarski(k1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),X1)),k1_xboole_0)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.45  fof(c_0_45, plain, ![X13]:(~v1_relat_1(X13)|k4_relat_1(k4_relat_1(X13))=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).
% 0.19/0.45  cnf(c_0_46, plain, (v1_xboole_0(k4_relat_1(X1))|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.45  cnf(c_0_47, plain, (r1_tarski(k1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),X1)),k1_xboole_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_24]), c_0_25])])).
% 0.19/0.45  cnf(c_0_48, plain, (k4_relat_1(k4_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.45  cnf(c_0_49, plain, (k4_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_17, c_0_46])).
% 0.19/0.45  cnf(c_0_50, plain, (r1_tarski(k1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),X1)),k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_47, c_0_24])).
% 0.19/0.45  cnf(c_0_51, plain, (k4_relat_1(k1_xboole_0)=X1|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.45  cnf(c_0_52, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_49])).
% 0.19/0.45  cnf(c_0_53, plain, (r1_tarski(k1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_25])).
% 0.19/0.45  cnf(c_0_54, plain, (k4_relat_1(k1_xboole_0)=k5_relat_1(k1_xboole_0,k1_xboole_0)|~v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_35]), c_0_25])])).
% 0.19/0.45  cnf(c_0_55, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_35]), c_0_25])])).
% 0.19/0.45  fof(c_0_56, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.19/0.45  cnf(c_0_57, plain, (k1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_53]), c_0_32])])).
% 0.19/0.45  cnf(c_0_58, plain, (k5_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0|~v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_54]), c_0_20]), c_0_25])]), c_0_55])).
% 0.19/0.45  fof(c_0_59, negated_conjecture, (v1_relat_1(esk2_0)&(k5_relat_1(k1_xboole_0,esk2_0)!=k1_xboole_0|k5_relat_1(esk2_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).
% 0.19/0.45  cnf(c_0_60, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_57]), c_0_25])])).
% 0.19/0.45  cnf(c_0_61, plain, (k5_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_41])).
% 0.19/0.45  cnf(c_0_62, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.45  fof(c_0_63, plain, ![X17, X18]:(~v1_relat_1(X17)|(~v1_relat_1(X18)|k4_relat_1(k5_relat_1(X17,X18))=k5_relat_1(k4_relat_1(X18),k4_relat_1(X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.19/0.45  cnf(c_0_64, plain, (v1_relat_1(k1_xboole_0)|~v1_xboole_0(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0))), inference(spm,[status(thm)],[c_0_60, c_0_24])).
% 0.19/0.45  cnf(c_0_65, plain, (k5_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_24]), c_0_25])])).
% 0.19/0.45  cnf(c_0_66, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,esk2_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_62])).
% 0.19/0.45  cnf(c_0_67, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.45  cnf(c_0_68, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_20]), c_0_25])])).
% 0.19/0.45  cnf(c_0_69, plain, (v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_65]), c_0_25])])).
% 0.19/0.45  cnf(c_0_70, negated_conjecture, (k1_relat_1(k5_relat_1(k1_xboole_0,esk2_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_66]), c_0_32])])).
% 0.19/0.45  cnf(c_0_71, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.45  cnf(c_0_72, plain, (v1_relat_1(k5_relat_1(k4_relat_1(X1),k4_relat_1(X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_67]), c_0_41])).
% 0.19/0.45  cnf(c_0_73, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69])])).
% 0.19/0.45  cnf(c_0_74, negated_conjecture, (k5_relat_1(k1_xboole_0,esk2_0)=k4_relat_1(k1_xboole_0)|~v1_relat_1(k5_relat_1(k1_xboole_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_70]), c_0_25])])).
% 0.19/0.45  cnf(c_0_75, plain, (k1_relat_1(k5_relat_1(k4_relat_1(X1),k4_relat_1(X2)))=k2_relat_1(k5_relat_1(X2,X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_67]), c_0_41])).
% 0.19/0.45  cnf(c_0_76, plain, (k1_xboole_0=X1|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(k4_relat_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_38])).
% 0.19/0.45  cnf(c_0_77, plain, (v1_relat_1(k5_relat_1(k4_relat_1(X1),k1_xboole_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_69])])).
% 0.19/0.45  cnf(c_0_78, negated_conjecture, (k5_relat_1(k1_xboole_0,esk2_0)=k1_xboole_0|~v1_relat_1(k5_relat_1(k1_xboole_0,esk2_0))), inference(rw,[status(thm)],[c_0_74, c_0_73])).
% 0.19/0.45  cnf(c_0_79, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k1_relat_1(k4_relat_1(X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_75]), c_0_38]), c_0_38])).
% 0.19/0.45  cnf(c_0_80, plain, (k1_xboole_0=X1|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_76, c_0_71])).
% 0.19/0.45  cnf(c_0_81, plain, (v1_relat_1(k5_relat_1(X1,k1_xboole_0))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_48]), c_0_38])).
% 0.19/0.45  cnf(c_0_82, negated_conjecture, (k5_relat_1(k1_xboole_0,esk2_0)!=k1_xboole_0|k5_relat_1(esk2_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.45  cnf(c_0_83, negated_conjecture, (k5_relat_1(k1_xboole_0,esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_41]), c_0_62]), c_0_69])])).
% 0.19/0.45  cnf(c_0_84, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,k1_xboole_0)),k1_xboole_0)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_69]), c_0_73]), c_0_20])).
% 0.19/0.45  cnf(c_0_85, plain, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(k5_relat_1(X1,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.45  cnf(c_0_86, negated_conjecture, (k5_relat_1(esk2_0,k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83])])).
% 0.19/0.45  cnf(c_0_87, negated_conjecture, (r1_tarski(k2_relat_1(k5_relat_1(esk2_0,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_84, c_0_62])).
% 0.19/0.45  cnf(c_0_88, negated_conjecture, (~v1_xboole_0(k2_relat_1(k5_relat_1(esk2_0,k1_xboole_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_62]), c_0_86])).
% 0.19/0.45  cnf(c_0_89, negated_conjecture, (k2_relat_1(k5_relat_1(esk2_0,k1_xboole_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_87]), c_0_32])])).
% 0.19/0.45  cnf(c_0_90, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89]), c_0_25])]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 91
% 0.19/0.45  # Proof object clause steps            : 63
% 0.19/0.45  # Proof object formula steps           : 28
% 0.19/0.45  # Proof object conjectures             : 15
% 0.19/0.45  # Proof object clause conjectures      : 12
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 16
% 0.19/0.45  # Proof object initial formulas used   : 14
% 0.19/0.45  # Proof object generating inferences   : 41
% 0.19/0.45  # Proof object simplifying inferences  : 55
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 14
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 19
% 0.19/0.45  # Removed in clause preprocessing      : 0
% 0.19/0.45  # Initial clauses in saturation        : 19
% 0.19/0.45  # Processed clauses                    : 526
% 0.19/0.45  # ...of these trivial                  : 15
% 0.19/0.45  # ...subsumed                          : 174
% 0.19/0.45  # ...remaining for further processing  : 337
% 0.19/0.45  # Other redundant clauses eliminated   : 2
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 6
% 0.19/0.45  # Backward-rewritten                   : 64
% 0.19/0.45  # Generated clauses                    : 5359
% 0.19/0.45  # ...of the previous two non-trivial   : 4730
% 0.19/0.45  # Contextual simplify-reflections      : 43
% 0.19/0.45  # Paramodulations                      : 5357
% 0.19/0.45  # Factorizations                       : 0
% 0.19/0.45  # Equation resolutions                 : 2
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 247
% 0.19/0.45  #    Positive orientable unit clauses  : 19
% 0.19/0.45  #    Positive unorientable unit clauses: 0
% 0.19/0.45  #    Negative unit clauses             : 4
% 0.19/0.45  #    Non-unit-clauses                  : 224
% 0.19/0.45  # Current number of unprocessed clauses: 4178
% 0.19/0.45  # ...number of literals in the above   : 15351
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 88
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 6087
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 5041
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 217
% 0.19/0.45  # Unit Clause-clause subsumption calls : 304
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 217
% 0.19/0.45  # BW rewrite match successes           : 15
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 96243
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.100 s
% 0.19/0.45  # System time              : 0.014 s
% 0.19/0.45  # Total time               : 0.114 s
% 0.19/0.45  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
