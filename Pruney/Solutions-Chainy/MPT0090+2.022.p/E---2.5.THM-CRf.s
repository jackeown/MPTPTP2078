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
% DateTime   : Thu Dec  3 10:33:45 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 537 expanded)
%              Number of clauses        :   49 ( 246 expanded)
%              Number of leaves         :   15 ( 146 expanded)
%              Depth                    :   16
%              Number of atoms          :  152 ( 891 expanded)
%              Number of equality atoms :   71 ( 441 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(t6_xboole_0,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t81_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t83_xboole_1,conjecture,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t67_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(t54_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(c_0_15,plain,(
    ! [X30,X31] :
      ( ~ r2_hidden(X30,X31)
      | ~ v1_xboole_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_16,plain,(
    ! [X6,X7] :
      ( ( r2_hidden(esk1_2(X6,X7),X7)
        | ~ r2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_2(X6,X7),X6)
        | ~ r2_xboole_0(X6,X7) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | ~ r2_xboole_0(X4,X5) )
      & ( X4 != X5
        | ~ r2_xboole_0(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | X4 = X5
        | r2_xboole_0(X4,X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

fof(c_0_20,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | r1_tarski(k4_xboole_0(X12,X11),k4_xboole_0(X12,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

fof(c_0_21,plain,(
    ! [X15] : k4_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_22,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X13,X14] :
      ( ( k4_xboole_0(X13,X14) != k1_xboole_0
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | k4_xboole_0(X13,X14) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X16,X17,X18] : k4_xboole_0(k4_xboole_0(X16,X17),X18) = k4_xboole_0(X16,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_30,plain,(
    ! [X32,X33,X34] :
      ( ~ r1_xboole_0(X32,k4_xboole_0(X33,X34))
      | r1_xboole_0(X33,k4_xboole_0(X32,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_xboole_0(X1,X2)
      <=> k4_xboole_0(X1,X2) = X1 ) ),
    inference(assume_negation,[status(cth)],[t83_xboole_1])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X2,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,negated_conjecture,
    ( ( ~ r1_xboole_0(esk2_0,esk3_0)
      | k4_xboole_0(esk2_0,esk3_0) != esk2_0 )
    & ( r1_xboole_0(esk2_0,esk3_0)
      | k4_xboole_0(esk2_0,esk3_0) = esk2_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X1,X3)
    | ~ v1_xboole_0(k4_xboole_0(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_26])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_41,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_tarski(X25,X26)
      | ~ r1_tarski(X25,X27)
      | ~ r1_xboole_0(X26,X27)
      | X25 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_27]),c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0)
    | k4_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(k2_xboole_0(X3,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = esk2_0
    | r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | k4_xboole_0(k2_xboole_0(X3,X1),X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_49,plain,(
    ! [X22,X23,X24] : k4_xboole_0(X22,k3_xboole_0(X23,X24)) = k2_xboole_0(k4_xboole_0(X22,X23),k4_xboole_0(X22,X24)) ),
    inference(variable_rename,[status(thm)],[t54_xboole_1])).

fof(c_0_50,plain,(
    ! [X19,X20,X21] : k4_xboole_0(X19,k4_xboole_0(X20,X21)) = k2_xboole_0(k4_xboole_0(X19,X20),k3_xboole_0(X19,X21)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = esk2_0
    | X1 = k1_xboole_0
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | k2_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_27]),c_0_27])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = esk2_0
    | X1 = k1_xboole_0
    | k4_xboole_0(X1,esk3_0) != k1_xboole_0
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_45])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | k4_xboole_0(X1,k3_xboole_0(X3,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_54])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k4_xboole_0(X1,k4_xboole_0(X3,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = esk2_0
    | X1 = k1_xboole_0
    | k4_xboole_0(X1,esk3_0) != k1_xboole_0
    | k4_xboole_0(X1,esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_45])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_27]),c_0_59]),c_0_27])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = esk2_0
    | k3_xboole_0(X1,esk3_0) = k1_xboole_0
    | k4_xboole_0(k3_xboole_0(X1,esk3_0),esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_63])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_39])).

cnf(c_0_68,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = k1_xboole_0
    | k4_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_63,c_0_67])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_27])).

fof(c_0_71,plain,(
    ! [X28,X29] : r1_xboole_0(k4_xboole_0(X28,X29),X29) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0)) = k4_xboole_0(esk2_0,X1)
    | k4_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_68]),c_0_69])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_70])).

cnf(c_0_74,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_27]),c_0_70])])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk3_0)
    | k4_xboole_0(esk2_0,esk3_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_75])]),c_0_77])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.13/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.026 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 0.13/0.39  fof(t6_xboole_0, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&![X3]:~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 0.13/0.39  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.13/0.39  fof(t34_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 0.13/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.39  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 0.13/0.39  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.13/0.39  fof(t81_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 0.13/0.39  fof(t83_xboole_1, conjecture, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.13/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.39  fof(t67_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 0.13/0.39  fof(t54_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_xboole_1)).
% 0.13/0.39  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.13/0.39  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.13/0.39  fof(c_0_15, plain, ![X30, X31]:(~r2_hidden(X30,X31)|~v1_xboole_0(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 0.13/0.39  fof(c_0_16, plain, ![X6, X7]:((r2_hidden(esk1_2(X6,X7),X7)|~r2_xboole_0(X6,X7))&(~r2_hidden(esk1_2(X6,X7),X6)|~r2_xboole_0(X6,X7))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).
% 0.13/0.39  cnf(c_0_17, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  fof(c_0_19, plain, ![X4, X5]:(((r1_tarski(X4,X5)|~r2_xboole_0(X4,X5))&(X4!=X5|~r2_xboole_0(X4,X5)))&(~r1_tarski(X4,X5)|X4=X5|r2_xboole_0(X4,X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.13/0.39  fof(c_0_20, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|r1_tarski(k4_xboole_0(X12,X11),k4_xboole_0(X12,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).
% 0.13/0.39  fof(c_0_21, plain, ![X15]:k4_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.39  fof(c_0_22, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.39  cnf(c_0_23, plain, (~v1_xboole_0(X1)|~r2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.39  cnf(c_0_24, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  fof(c_0_25, plain, ![X13, X14]:((k4_xboole_0(X13,X14)!=k1_xboole_0|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|k4_xboole_0(X13,X14)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 0.13/0.39  cnf(c_0_26, plain, (r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_27, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_28, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  fof(c_0_29, plain, ![X16, X17, X18]:k4_xboole_0(k4_xboole_0(X16,X17),X18)=k4_xboole_0(X16,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.13/0.39  fof(c_0_30, plain, ![X32, X33, X34]:(~r1_xboole_0(X32,k4_xboole_0(X33,X34))|r1_xboole_0(X33,k4_xboole_0(X32,X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).
% 0.13/0.39  fof(c_0_31, negated_conjecture, ~(![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1)), inference(assume_negation,[status(cth)],[t83_xboole_1])).
% 0.13/0.39  cnf(c_0_32, plain, (X1=X2|~v1_xboole_0(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.39  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_34, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.13/0.39  cnf(c_0_35, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_36, plain, (r1_xboole_0(X2,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  fof(c_0_37, negated_conjecture, ((~r1_xboole_0(esk2_0,esk3_0)|k4_xboole_0(esk2_0,esk3_0)!=esk2_0)&(r1_xboole_0(esk2_0,esk3_0)|k4_xboole_0(esk2_0,esk3_0)=esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.13/0.39  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=k4_xboole_0(X1,X3)|~v1_xboole_0(k4_xboole_0(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_32, c_0_26])).
% 0.13/0.39  cnf(c_0_39, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.13/0.39  cnf(c_0_40, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.39  fof(c_0_41, plain, ![X25, X26, X27]:(~r1_tarski(X25,X26)|~r1_tarski(X25,X27)|~r1_xboole_0(X26,X27)|X25=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).
% 0.13/0.39  cnf(c_0_42, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_27]), c_0_27])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)|k4_xboole_0(esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.39  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(k2_xboole_0(X3,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.13/0.39  cnf(c_0_45, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_46, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=esk2_0|r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.39  cnf(c_0_48, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|k4_xboole_0(k2_xboole_0(X3,X1),X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.39  fof(c_0_49, plain, ![X22, X23, X24]:k4_xboole_0(X22,k3_xboole_0(X23,X24))=k2_xboole_0(k4_xboole_0(X22,X23),k4_xboole_0(X22,X24)), inference(variable_rename,[status(thm)],[t54_xboole_1])).
% 0.13/0.39  fof(c_0_50, plain, ![X19, X20, X21]:k4_xboole_0(X19,k4_xboole_0(X20,X21))=k2_xboole_0(k4_xboole_0(X19,X20),k3_xboole_0(X19,X21)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=esk2_0|X1=k1_xboole_0|~r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.39  cnf(c_0_52, plain, (X1=k1_xboole_0|k2_xboole_0(X2,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_27]), c_0_27])).
% 0.13/0.39  cnf(c_0_53, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.39  cnf(c_0_54, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_34, c_0_27])).
% 0.13/0.39  cnf(c_0_55, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=esk2_0|X1=k1_xboole_0|k4_xboole_0(X1,esk3_0)!=k1_xboole_0|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_51, c_0_45])).
% 0.13/0.39  cnf(c_0_57, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|k4_xboole_0(X1,k3_xboole_0(X3,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.39  cnf(c_0_58, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_54])).
% 0.13/0.39  cnf(c_0_59, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_28])).
% 0.13/0.39  cnf(c_0_60, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|k4_xboole_0(X1,k4_xboole_0(X3,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_55])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=esk2_0|X1=k1_xboole_0|k4_xboole_0(X1,esk3_0)!=k1_xboole_0|k4_xboole_0(X1,esk2_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_45])).
% 0.13/0.39  cnf(c_0_62, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.13/0.39  cnf(c_0_63, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_27]), c_0_59]), c_0_27])).
% 0.13/0.39  cnf(c_0_64, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_27])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=esk2_0|k3_xboole_0(X1,esk3_0)=k1_xboole_0|k4_xboole_0(k3_xboole_0(X1,esk3_0),esk2_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.13/0.39  cnf(c_0_66, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_63])).
% 0.13/0.39  cnf(c_0_67, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_39])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=k1_xboole_0|k4_xboole_0(esk2_0,esk3_0)=esk2_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.13/0.39  cnf(c_0_69, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_63, c_0_67])).
% 0.13/0.39  cnf(c_0_70, plain, (k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_27])).
% 0.13/0.39  fof(c_0_71, plain, ![X28, X29]:r1_xboole_0(k4_xboole_0(X28,X29),X29), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.13/0.39  cnf(c_0_72, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0))=k4_xboole_0(esk2_0,X1)|k4_xboole_0(esk2_0,esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_68]), c_0_69])).
% 0.13/0.39  cnf(c_0_73, plain, (k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_70])).
% 0.13/0.39  cnf(c_0_74, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.13/0.39  cnf(c_0_75, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_27]), c_0_70])])).
% 0.13/0.39  cnf(c_0_76, negated_conjecture, (~r1_xboole_0(esk2_0,esk3_0)|k4_xboole_0(esk2_0,esk3_0)!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.13/0.39  cnf(c_0_78, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_75])]), c_0_77])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 79
% 0.13/0.39  # Proof object clause steps            : 49
% 0.13/0.39  # Proof object formula steps           : 30
% 0.13/0.39  # Proof object conjectures             : 15
% 0.13/0.39  # Proof object clause conjectures      : 12
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 17
% 0.13/0.39  # Proof object initial formulas used   : 15
% 0.13/0.39  # Proof object generating inferences   : 31
% 0.13/0.39  # Proof object simplifying inferences  : 17
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 15
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 20
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 20
% 0.13/0.39  # Processed clauses                    : 240
% 0.13/0.39  # ...of these trivial                  : 4
% 0.13/0.39  # ...subsumed                          : 90
% 0.13/0.39  # ...remaining for further processing  : 145
% 0.13/0.39  # Other redundant clauses eliminated   : 1
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 5
% 0.13/0.39  # Backward-rewritten                   : 25
% 0.13/0.39  # Generated clauses                    : 1023
% 0.13/0.39  # ...of the previous two non-trivial   : 758
% 0.13/0.39  # Contextual simplify-reflections      : 2
% 0.13/0.39  # Paramodulations                      : 1022
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 1
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
% 0.13/0.39  # Current number of processed clauses  : 94
% 0.13/0.39  #    Positive orientable unit clauses  : 34
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 3
% 0.13/0.39  #    Non-unit-clauses                  : 57
% 0.13/0.39  # Current number of unprocessed clauses: 539
% 0.13/0.39  # ...number of literals in the above   : 1088
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 50
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 793
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 716
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 93
% 0.13/0.39  # Unit Clause-clause subsumption calls : 39
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 71
% 0.13/0.39  # BW rewrite match successes           : 8
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 9744
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.043 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.047 s
% 0.13/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
