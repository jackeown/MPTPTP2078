%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:07 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  106 (2445 expanded)
%              Number of clauses        :   69 (1079 expanded)
%              Number of leaves         :   18 ( 680 expanded)
%              Depth                    :   14
%              Number of atoms          :  129 (2603 expanded)
%              Number of equality atoms :   83 (2383 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t82_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(t97_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k4_xboole_0(X1,X2),X3)
        & r1_tarski(k4_xboole_0(X2,X1),X3) )
     => r1_tarski(k5_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(c_0_18,plain,(
    ! [X13] : k3_xboole_0(X13,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_19,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_20,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k3_xboole_0(X21,X22)) = k4_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_21,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_22,plain,(
    ! [X25,X26,X27] : k3_xboole_0(X25,k4_xboole_0(X26,X27)) = k4_xboole_0(k3_xboole_0(X25,X26),X27) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X17] : k4_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X31,X32] :
      ( ( ~ r1_xboole_0(X31,X32)
        | k4_xboole_0(X31,X32) = X31 )
      & ( k4_xboole_0(X31,X32) != X31
        | r1_xboole_0(X31,X32) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_32,plain,(
    ! [X29,X30] : r1_xboole_0(k4_xboole_0(X29,X30),k4_xboole_0(X30,X29)) ),
    inference(variable_rename,[status(thm)],[t82_xboole_1])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_24]),c_0_24])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_24]),c_0_24])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(k4_xboole_0(X1,X2),X3)
          & r1_tarski(k4_xboole_0(X2,X1),X3) )
       => r1_tarski(k5_xboole_0(X1,X2),X3) ) ),
    inference(assume_negation,[status(cth)],[t97_xboole_1])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_41,plain,(
    ! [X37,X38] : k2_xboole_0(X37,X38) = k5_xboole_0(k5_xboole_0(X37,X38),k3_xboole_0(X37,X38)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_42,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_43,plain,(
    ! [X11,X12] :
      ( ( k4_xboole_0(X11,X12) != k1_xboole_0
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | k4_xboole_0(X11,X12) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_30]),c_0_36])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_46,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0)
    & r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0)
    & ~ r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

fof(c_0_47,plain,(
    ! [X33,X34,X35] : k5_xboole_0(k5_xboole_0(X33,X34),X35) = k5_xboole_0(X33,k5_xboole_0(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_40]),c_0_35]),c_0_33]),c_0_35]),c_0_36]),c_0_30]),c_0_36])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_51,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(k4_xboole_0(X18,X19),X20)
      | r1_tarski(X18,k2_xboole_0(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_30]),c_0_30]),c_0_36])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_34]),c_0_40]),c_0_36])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_48]),c_0_30])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_24]),c_0_50]),c_0_50])).

fof(c_0_60,plain,(
    ! [X10] : k2_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_63,plain,(
    ! [X28] : k5_xboole_0(X28,k1_xboole_0) = X28 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_64,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_65,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_54])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_33])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_68,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X3),k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_50]),c_0_50]),c_0_50]),c_0_50])).

cnf(c_0_69,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_58]),c_0_36]),c_0_30])).

cnf(c_0_70,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_59,c_0_35])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_36]),c_0_62])])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_75,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | r1_tarski(k4_xboole_0(X16,X15),k4_xboole_0(X16,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

cnf(c_0_76,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_77,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk1_0))) = k4_xboole_0(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_67]),c_0_30])).

cnf(c_0_78,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X3,X2)),k4_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X2))),k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_58]),c_0_58])).

cnf(c_0_79,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_36]),c_0_36]),c_0_71]),c_0_36]),c_0_30]),c_0_53]),c_0_36]),c_0_71]),c_0_30]),c_0_36]),c_0_30]),c_0_71])).

cnf(c_0_80,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_72])).

cnf(c_0_81,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_73,c_0_50])).

cnf(c_0_82,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_50]),c_0_50])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_84,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_86,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X1)),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_36]),c_0_36]),c_0_71]),c_0_53]),c_0_36]),c_0_71]),c_0_30]),c_0_79]),c_0_80]),c_0_79])).

cnf(c_0_87,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_81,c_0_30])).

cnf(c_0_88,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))))) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_82])).

cnf(c_0_89,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_34]),c_0_35])).

cnf(c_0_90,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_34])).

cnf(c_0_91,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_83])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk3_0),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),X2))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_93,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_86]),c_0_80]),c_0_30])).

cnf(c_0_94,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_87,c_0_53])).

cnf(c_0_95,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk2_0))) = k4_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_91]),c_0_30])).

cnf(c_0_97,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X2) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_69]),c_0_58]),c_0_58])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1)),esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2)),X1)) = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_36]),c_0_36]),c_0_71]),c_0_30]),c_0_36]),c_0_71]),c_0_53]),c_0_94]),c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk2_0))) = k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_91]),c_0_94]),c_0_96]),c_0_69]),c_0_94]),c_0_58]),c_0_96]),c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1)),k2_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk2_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_91]),c_0_94]),c_0_58]),c_0_94]),c_0_69]),c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_101,c_0_50])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_45]),c_0_104]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.16/0.36  % Computer   : n022.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 10:00:11 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  # Version: 2.5pre002
% 0.16/0.36  # No SInE strategy applied
% 0.16/0.36  # Trying AutoSched0 for 299 seconds
% 2.61/2.78  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 2.61/2.78  # and selection function SelectNewComplexAHP.
% 2.61/2.78  #
% 2.61/2.78  # Preprocessing time       : 0.027 s
% 2.61/2.78  # Presaturation interreduction done
% 2.61/2.78  
% 2.61/2.78  # Proof found!
% 2.61/2.78  # SZS status Theorem
% 2.61/2.78  # SZS output start CNFRefutation
% 2.61/2.78  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.61/2.78  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.61/2.78  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.61/2.78  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.61/2.78  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.61/2.78  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.61/2.78  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.61/2.78  fof(t82_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_xboole_1)).
% 2.61/2.78  fof(t97_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(k4_xboole_0(X1,X2),X3)&r1_tarski(k4_xboole_0(X2,X1),X3))=>r1_tarski(k5_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_xboole_1)).
% 2.61/2.78  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 2.61/2.78  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.61/2.78  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.61/2.78  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.61/2.78  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.61/2.78  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.61/2.78  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.61/2.78  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.61/2.78  fof(t34_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 2.61/2.78  fof(c_0_18, plain, ![X13]:k3_xboole_0(X13,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 2.61/2.78  fof(c_0_19, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.61/2.78  fof(c_0_20, plain, ![X21, X22]:k4_xboole_0(X21,k3_xboole_0(X21,X22))=k4_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 2.61/2.78  fof(c_0_21, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.61/2.78  fof(c_0_22, plain, ![X25, X26, X27]:k3_xboole_0(X25,k4_xboole_0(X26,X27))=k4_xboole_0(k3_xboole_0(X25,X26),X27), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 2.61/2.78  cnf(c_0_23, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.61/2.78  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.61/2.78  fof(c_0_25, plain, ![X17]:k4_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t3_boole])).
% 2.61/2.78  cnf(c_0_26, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.61/2.78  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.61/2.78  cnf(c_0_28, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.61/2.78  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 2.61/2.78  cnf(c_0_30, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.61/2.78  fof(c_0_31, plain, ![X31, X32]:((~r1_xboole_0(X31,X32)|k4_xboole_0(X31,X32)=X31)&(k4_xboole_0(X31,X32)!=X31|r1_xboole_0(X31,X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 2.61/2.78  fof(c_0_32, plain, ![X29, X30]:r1_xboole_0(k4_xboole_0(X29,X30),k4_xboole_0(X30,X29)), inference(variable_rename,[status(thm)],[t82_xboole_1])).
% 2.61/2.78  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_24])).
% 2.61/2.78  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_24]), c_0_24])).
% 2.61/2.78  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_24]), c_0_24])).
% 2.61/2.78  cnf(c_0_36, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 2.61/2.78  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.61/2.78  cnf(c_0_38, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.61/2.78  fof(c_0_39, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(k4_xboole_0(X1,X2),X3)&r1_tarski(k4_xboole_0(X2,X1),X3))=>r1_tarski(k5_xboole_0(X1,X2),X3))), inference(assume_negation,[status(cth)],[t97_xboole_1])).
% 2.61/2.78  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 2.61/2.78  fof(c_0_41, plain, ![X37, X38]:k2_xboole_0(X37,X38)=k5_xboole_0(k5_xboole_0(X37,X38),k3_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 2.61/2.78  fof(c_0_42, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 2.61/2.78  fof(c_0_43, plain, ![X11, X12]:((k4_xboole_0(X11,X12)!=k1_xboole_0|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|k4_xboole_0(X11,X12)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 2.61/2.78  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)))=k4_xboole_0(k1_xboole_0,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_30]), c_0_36])).
% 2.61/2.78  cnf(c_0_45, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.61/2.78  fof(c_0_46, negated_conjecture, ((r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0)&r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0))&~r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 2.61/2.78  fof(c_0_47, plain, ![X33, X34, X35]:k5_xboole_0(k5_xboole_0(X33,X34),X35)=k5_xboole_0(X33,k5_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 2.61/2.78  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_40]), c_0_35]), c_0_33]), c_0_35]), c_0_36]), c_0_30]), c_0_36])).
% 2.61/2.78  cnf(c_0_49, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.61/2.78  cnf(c_0_50, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.61/2.78  fof(c_0_51, plain, ![X18, X19, X20]:(~r1_tarski(k4_xboole_0(X18,X19),X20)|r1_tarski(X18,k2_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 2.61/2.78  cnf(c_0_52, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.61/2.78  cnf(c_0_53, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_30]), c_0_30]), c_0_36])).
% 2.61/2.78  cnf(c_0_54, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_34]), c_0_40]), c_0_36])).
% 2.61/2.78  cnf(c_0_55, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.61/2.78  cnf(c_0_56, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 2.61/2.78  cnf(c_0_57, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.61/2.78  cnf(c_0_58, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_48]), c_0_30])).
% 2.61/2.78  cnf(c_0_59, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_24]), c_0_50]), c_0_50])).
% 2.61/2.78  fof(c_0_60, plain, ![X10]:k2_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 2.61/2.78  cnf(c_0_61, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 2.61/2.78  cnf(c_0_62, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 2.61/2.78  fof(c_0_63, plain, ![X28]:k5_xboole_0(X28,k1_xboole_0)=X28, inference(variable_rename,[status(thm)],[t5_boole])).
% 2.61/2.78  fof(c_0_64, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 2.61/2.78  cnf(c_0_65, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_52, c_0_54])).
% 2.61/2.78  cnf(c_0_66, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_35, c_0_33])).
% 2.61/2.78  cnf(c_0_67, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 2.61/2.78  cnf(c_0_68, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X3),k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))))=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_50]), c_0_50]), c_0_50]), c_0_50])).
% 2.61/2.78  cnf(c_0_69, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_58]), c_0_36]), c_0_30])).
% 2.61/2.78  cnf(c_0_70, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_59, c_0_35])).
% 2.61/2.78  cnf(c_0_71, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_60])).
% 2.61/2.78  cnf(c_0_72, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_36]), c_0_62])])).
% 2.61/2.78  cnf(c_0_73, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_63])).
% 2.61/2.78  cnf(c_0_74, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 2.61/2.78  fof(c_0_75, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|r1_tarski(k4_xboole_0(X16,X15),k4_xboole_0(X16,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).
% 2.61/2.78  cnf(c_0_76, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 2.61/2.78  cnf(c_0_77, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk1_0)))=k4_xboole_0(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_67]), c_0_30])).
% 2.61/2.78  cnf(c_0_78, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X3,X2)),k4_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))))=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X2))),k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_58]), c_0_58])).
% 2.61/2.78  cnf(c_0_79, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_36]), c_0_36]), c_0_71]), c_0_36]), c_0_30]), c_0_53]), c_0_36]), c_0_71]), c_0_30]), c_0_36]), c_0_30]), c_0_71])).
% 2.61/2.78  cnf(c_0_80, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_72])).
% 2.61/2.78  cnf(c_0_81, plain, (k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[c_0_73, c_0_50])).
% 2.61/2.78  cnf(c_0_82, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_50]), c_0_50])).
% 2.61/2.78  cnf(c_0_83, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 2.61/2.78  cnf(c_0_84, plain, (r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 2.61/2.78  cnf(c_0_85, negated_conjecture, (r1_tarski(k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1),esk3_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 2.61/2.78  cnf(c_0_86, plain, (k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X1)),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_36]), c_0_36]), c_0_71]), c_0_53]), c_0_36]), c_0_71]), c_0_30]), c_0_79]), c_0_80]), c_0_79])).
% 2.61/2.78  cnf(c_0_87, plain, (k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[c_0_81, c_0_30])).
% 2.61/2.78  cnf(c_0_88, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))))))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_70, c_0_82])).
% 2.61/2.78  cnf(c_0_89, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_34]), c_0_35])).
% 2.61/2.78  cnf(c_0_90, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))))))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_70, c_0_34])).
% 2.61/2.78  cnf(c_0_91, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_83])).
% 2.61/2.78  cnf(c_0_92, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk3_0),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),X2)))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 2.61/2.78  cnf(c_0_93, plain, (k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_86]), c_0_80]), c_0_30])).
% 2.61/2.78  cnf(c_0_94, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_87, c_0_53])).
% 2.61/2.78  cnf(c_0_95, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])).
% 2.61/2.78  cnf(c_0_96, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk2_0)))=k4_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_91]), c_0_30])).
% 2.61/2.78  cnf(c_0_97, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X2)=k2_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_69]), c_0_58]), c_0_58])).
% 2.61/2.78  cnf(c_0_98, negated_conjecture, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1)),esk3_0),X1)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 2.61/2.78  cnf(c_0_99, plain, (k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2)),X1))=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_36]), c_0_36]), c_0_71]), c_0_30]), c_0_36]), c_0_71]), c_0_53]), c_0_94]), c_0_95])).
% 2.61/2.78  cnf(c_0_100, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk2_0)))=k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_91]), c_0_94]), c_0_96]), c_0_69]), c_0_94]), c_0_58]), c_0_96]), c_0_97])).
% 2.61/2.78  cnf(c_0_101, negated_conjecture, (~r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 2.61/2.78  cnf(c_0_102, negated_conjecture, (r1_tarski(k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1)),k2_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_61, c_0_98])).
% 2.61/2.78  cnf(c_0_103, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk2_0))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_91]), c_0_94]), c_0_58]), c_0_94]), c_0_69]), c_0_100])).
% 2.61/2.78  cnf(c_0_104, negated_conjecture, (~r1_tarski(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk3_0)), inference(rw,[status(thm)],[c_0_101, c_0_50])).
% 2.61/2.78  cnf(c_0_105, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_45]), c_0_104]), ['proof']).
% 2.61/2.78  # SZS output end CNFRefutation
% 2.61/2.78  # Proof object total steps             : 106
% 2.61/2.78  # Proof object clause steps            : 69
% 2.61/2.78  # Proof object formula steps           : 37
% 2.61/2.78  # Proof object conjectures             : 18
% 2.61/2.78  # Proof object clause conjectures      : 15
% 2.61/2.78  # Proof object formula conjectures     : 3
% 2.61/2.78  # Proof object initial clauses used    : 21
% 2.61/2.78  # Proof object initial formulas used   : 18
% 2.61/2.78  # Proof object generating inferences   : 35
% 2.61/2.78  # Proof object simplifying inferences  : 90
% 2.61/2.78  # Training examples: 0 positive, 0 negative
% 2.61/2.78  # Parsed axioms                        : 20
% 2.61/2.78  # Removed by relevancy pruning/SinE    : 0
% 2.61/2.78  # Initial clauses                      : 24
% 2.61/2.78  # Removed in clause preprocessing      : 2
% 2.61/2.78  # Initial clauses in saturation        : 22
% 2.61/2.78  # Processed clauses                    : 6559
% 2.61/2.78  # ...of these trivial                  : 3292
% 2.61/2.78  # ...subsumed                          : 931
% 2.61/2.78  # ...remaining for further processing  : 2336
% 2.61/2.78  # Other redundant clauses eliminated   : 0
% 2.61/2.78  # Clauses deleted for lack of memory   : 0
% 2.61/2.78  # Backward-subsumed                    : 1
% 2.61/2.78  # Backward-rewritten                   : 832
% 2.61/2.78  # Generated clauses                    : 428745
% 2.61/2.78  # ...of the previous two non-trivial   : 189148
% 2.61/2.78  # Contextual simplify-reflections      : 0
% 2.61/2.78  # Paramodulations                      : 428738
% 2.61/2.78  # Factorizations                       : 0
% 2.61/2.78  # Equation resolutions                 : 7
% 2.61/2.78  # Propositional unsat checks           : 0
% 2.61/2.78  #    Propositional check models        : 0
% 2.61/2.78  #    Propositional check unsatisfiable : 0
% 2.61/2.78  #    Propositional clauses             : 0
% 2.61/2.78  #    Propositional clauses after purity: 0
% 2.61/2.78  #    Propositional unsat core size     : 0
% 2.61/2.78  #    Propositional preprocessing time  : 0.000
% 2.61/2.78  #    Propositional encoding time       : 0.000
% 2.61/2.78  #    Propositional solver time         : 0.000
% 2.61/2.78  #    Success case prop preproc time    : 0.000
% 2.61/2.78  #    Success case prop encoding time   : 0.000
% 2.61/2.78  #    Success case prop solver time     : 0.000
% 2.61/2.78  # Current number of processed clauses  : 1482
% 2.61/2.78  #    Positive orientable unit clauses  : 1372
% 2.61/2.78  #    Positive unorientable unit clauses: 17
% 2.61/2.78  #    Negative unit clauses             : 1
% 2.61/2.78  #    Non-unit-clauses                  : 92
% 2.61/2.78  # Current number of unprocessed clauses: 181332
% 2.61/2.78  # ...number of literals in the above   : 186082
% 2.61/2.78  # Current number of archived formulas  : 0
% 2.61/2.78  # Current number of archived clauses   : 856
% 2.61/2.78  # Clause-clause subsumption calls (NU) : 2580
% 2.61/2.78  # Rec. Clause-clause subsumption calls : 2580
% 2.61/2.78  # Non-unit clause-clause subsumptions  : 866
% 2.61/2.78  # Unit Clause-clause subsumption calls : 2033
% 2.61/2.78  # Rewrite failures with RHS unbound    : 0
% 2.61/2.78  # BW rewrite match attempts            : 16429
% 2.61/2.78  # BW rewrite match successes           : 1796
% 2.61/2.78  # Condensation attempts                : 0
% 2.61/2.78  # Condensation successes               : 0
% 2.61/2.78  # Termbank termtop insertions          : 8373738
% 2.61/2.79  
% 2.61/2.79  # -------------------------------------------------
% 2.61/2.79  # User time                : 2.321 s
% 2.61/2.79  # System time              : 0.110 s
% 2.61/2.79  # Total time               : 2.431 s
% 2.61/2.79  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
