%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:07 EST 2020

% Result     : Theorem 5.52s
% Output     : CNFRefutation 5.52s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t82_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

fof(t97_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k4_xboole_0(X1,X2),X3)
        & r1_tarski(k4_xboole_0(X2,X1),X3) )
     => r1_tarski(k5_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(c_0_18,plain,(
    ! [X11] : k3_xboole_0(X11,k1_xboole_0) = k1_xboole_0 ),
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
    ! [X15,X16] :
      ( ( k4_xboole_0(X15,X16) != k1_xboole_0
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | k4_xboole_0(X15,X16) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

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
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | r1_tarski(k4_xboole_0(X14,X13),k4_xboole_0(X14,X12)) ) ),
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
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:23:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 5.52/5.71  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 5.52/5.71  # and selection function SelectNewComplexAHP.
% 5.52/5.71  #
% 5.52/5.71  # Preprocessing time       : 0.027 s
% 5.52/5.71  # Presaturation interreduction done
% 5.52/5.71  
% 5.52/5.71  # Proof found!
% 5.52/5.71  # SZS status Theorem
% 5.52/5.71  # SZS output start CNFRefutation
% 5.52/5.71  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.52/5.71  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.52/5.71  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.52/5.71  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.52/5.71  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 5.52/5.71  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.52/5.71  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.52/5.71  fof(t82_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 5.52/5.71  fof(t97_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(k4_xboole_0(X1,X2),X3)&r1_tarski(k4_xboole_0(X2,X1),X3))=>r1_tarski(k5_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_xboole_1)).
% 5.52/5.71  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 5.52/5.71  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 5.52/5.71  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 5.52/5.71  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.52/5.71  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.52/5.71  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.52/5.71  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.52/5.71  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.52/5.71  fof(t34_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 5.52/5.71  fof(c_0_18, plain, ![X11]:k3_xboole_0(X11,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 5.52/5.71  fof(c_0_19, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 5.52/5.71  fof(c_0_20, plain, ![X21, X22]:k4_xboole_0(X21,k3_xboole_0(X21,X22))=k4_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 5.52/5.71  fof(c_0_21, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 5.52/5.71  fof(c_0_22, plain, ![X25, X26, X27]:k3_xboole_0(X25,k4_xboole_0(X26,X27))=k4_xboole_0(k3_xboole_0(X25,X26),X27), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 5.52/5.71  cnf(c_0_23, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.52/5.71  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 5.52/5.71  fof(c_0_25, plain, ![X17]:k4_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t3_boole])).
% 5.52/5.71  cnf(c_0_26, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.52/5.71  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 5.52/5.71  cnf(c_0_28, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.52/5.71  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 5.52/5.71  cnf(c_0_30, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 5.52/5.71  fof(c_0_31, plain, ![X31, X32]:((~r1_xboole_0(X31,X32)|k4_xboole_0(X31,X32)=X31)&(k4_xboole_0(X31,X32)!=X31|r1_xboole_0(X31,X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 5.52/5.71  fof(c_0_32, plain, ![X29, X30]:r1_xboole_0(k4_xboole_0(X29,X30),k4_xboole_0(X30,X29)), inference(variable_rename,[status(thm)],[t82_xboole_1])).
% 5.52/5.71  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_24])).
% 5.52/5.71  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_24]), c_0_24])).
% 5.52/5.71  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_24]), c_0_24])).
% 5.52/5.71  cnf(c_0_36, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 5.52/5.71  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 5.52/5.71  cnf(c_0_38, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 5.52/5.71  fof(c_0_39, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(k4_xboole_0(X1,X2),X3)&r1_tarski(k4_xboole_0(X2,X1),X3))=>r1_tarski(k5_xboole_0(X1,X2),X3))), inference(assume_negation,[status(cth)],[t97_xboole_1])).
% 5.52/5.71  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 5.52/5.71  fof(c_0_41, plain, ![X37, X38]:k2_xboole_0(X37,X38)=k5_xboole_0(k5_xboole_0(X37,X38),k3_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 5.52/5.71  fof(c_0_42, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 5.52/5.71  fof(c_0_43, plain, ![X15, X16]:((k4_xboole_0(X15,X16)!=k1_xboole_0|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|k4_xboole_0(X15,X16)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 5.52/5.71  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)))=k4_xboole_0(k1_xboole_0,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_30]), c_0_36])).
% 5.52/5.71  cnf(c_0_45, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 5.52/5.71  fof(c_0_46, negated_conjecture, ((r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0)&r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0))&~r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 5.52/5.71  fof(c_0_47, plain, ![X33, X34, X35]:k5_xboole_0(k5_xboole_0(X33,X34),X35)=k5_xboole_0(X33,k5_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 5.52/5.71  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_40]), c_0_35]), c_0_33]), c_0_35]), c_0_36]), c_0_30]), c_0_36])).
% 5.52/5.71  cnf(c_0_49, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.52/5.71  cnf(c_0_50, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 5.52/5.71  fof(c_0_51, plain, ![X18, X19, X20]:(~r1_tarski(k4_xboole_0(X18,X19),X20)|r1_tarski(X18,k2_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 5.52/5.71  cnf(c_0_52, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 5.52/5.71  cnf(c_0_53, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_30]), c_0_30]), c_0_36])).
% 5.52/5.71  cnf(c_0_54, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_34]), c_0_40]), c_0_36])).
% 5.52/5.71  cnf(c_0_55, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 5.52/5.71  cnf(c_0_56, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,esk1_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 5.52/5.71  cnf(c_0_57, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 5.52/5.71  cnf(c_0_58, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_48]), c_0_30])).
% 5.52/5.71  cnf(c_0_59, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_24]), c_0_50]), c_0_50])).
% 5.52/5.71  fof(c_0_60, plain, ![X10]:k2_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 5.52/5.71  cnf(c_0_61, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 5.52/5.71  cnf(c_0_62, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 5.52/5.71  fof(c_0_63, plain, ![X28]:k5_xboole_0(X28,k1_xboole_0)=X28, inference(variable_rename,[status(thm)],[t5_boole])).
% 5.52/5.71  fof(c_0_64, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 5.52/5.71  cnf(c_0_65, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_52, c_0_54])).
% 5.52/5.71  cnf(c_0_66, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_35, c_0_33])).
% 5.52/5.71  cnf(c_0_67, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 5.52/5.71  cnf(c_0_68, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X3),k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))))=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_50]), c_0_50]), c_0_50]), c_0_50])).
% 5.52/5.71  cnf(c_0_69, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_58]), c_0_36]), c_0_30])).
% 5.52/5.71  cnf(c_0_70, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_59, c_0_35])).
% 5.52/5.71  cnf(c_0_71, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_60])).
% 5.52/5.71  cnf(c_0_72, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_36]), c_0_62])])).
% 5.52/5.71  cnf(c_0_73, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_63])).
% 5.52/5.71  cnf(c_0_74, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 5.52/5.71  fof(c_0_75, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|r1_tarski(k4_xboole_0(X14,X13),k4_xboole_0(X14,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).
% 5.52/5.71  cnf(c_0_76, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 5.52/5.71  cnf(c_0_77, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk1_0)))=k4_xboole_0(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_67]), c_0_30])).
% 5.52/5.71  cnf(c_0_78, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X3,X2)),k4_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))))=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X2))),k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_58]), c_0_58])).
% 5.52/5.71  cnf(c_0_79, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_36]), c_0_36]), c_0_71]), c_0_36]), c_0_30]), c_0_53]), c_0_36]), c_0_71]), c_0_30]), c_0_36]), c_0_30]), c_0_71])).
% 5.52/5.71  cnf(c_0_80, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_72])).
% 5.52/5.71  cnf(c_0_81, plain, (k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[c_0_73, c_0_50])).
% 5.52/5.71  cnf(c_0_82, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_50]), c_0_50])).
% 5.52/5.71  cnf(c_0_83, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 5.52/5.71  cnf(c_0_84, plain, (r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 5.52/5.71  cnf(c_0_85, negated_conjecture, (r1_tarski(k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1),esk3_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 5.52/5.71  cnf(c_0_86, plain, (k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X1)),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_36]), c_0_36]), c_0_71]), c_0_53]), c_0_36]), c_0_71]), c_0_30]), c_0_79]), c_0_80]), c_0_79])).
% 5.52/5.71  cnf(c_0_87, plain, (k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[c_0_81, c_0_30])).
% 5.52/5.71  cnf(c_0_88, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))))))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_70, c_0_82])).
% 5.52/5.71  cnf(c_0_89, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_34]), c_0_35])).
% 5.52/5.71  cnf(c_0_90, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))))))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_70, c_0_34])).
% 5.52/5.71  cnf(c_0_91, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_83])).
% 5.52/5.71  cnf(c_0_92, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk3_0),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),X2)))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 5.52/5.71  cnf(c_0_93, plain, (k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_86]), c_0_80]), c_0_30])).
% 5.52/5.71  cnf(c_0_94, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_87, c_0_53])).
% 5.52/5.71  cnf(c_0_95, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])).
% 5.52/5.71  cnf(c_0_96, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk2_0)))=k4_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_91]), c_0_30])).
% 5.52/5.71  cnf(c_0_97, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X2)=k2_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_69]), c_0_58]), c_0_58])).
% 5.52/5.71  cnf(c_0_98, negated_conjecture, (r1_tarski(k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1)),esk3_0),X1)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 5.52/5.71  cnf(c_0_99, plain, (k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2)),X1))=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_36]), c_0_36]), c_0_71]), c_0_30]), c_0_36]), c_0_71]), c_0_53]), c_0_94]), c_0_95])).
% 5.52/5.71  cnf(c_0_100, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk2_0)))=k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_91]), c_0_94]), c_0_96]), c_0_69]), c_0_94]), c_0_58]), c_0_96]), c_0_97])).
% 5.52/5.71  cnf(c_0_101, negated_conjecture, (~r1_tarski(k5_xboole_0(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 5.52/5.71  cnf(c_0_102, negated_conjecture, (r1_tarski(k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk2_0,esk1_0),X1)),k2_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_61, c_0_98])).
% 5.52/5.71  cnf(c_0_103, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,esk2_0))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_91]), c_0_94]), c_0_58]), c_0_94]), c_0_69]), c_0_100])).
% 5.52/5.71  cnf(c_0_104, negated_conjecture, (~r1_tarski(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk3_0)), inference(rw,[status(thm)],[c_0_101, c_0_50])).
% 5.52/5.71  cnf(c_0_105, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_45]), c_0_104]), ['proof']).
% 5.52/5.71  # SZS output end CNFRefutation
% 5.52/5.71  # Proof object total steps             : 106
% 5.52/5.71  # Proof object clause steps            : 69
% 5.52/5.71  # Proof object formula steps           : 37
% 5.52/5.71  # Proof object conjectures             : 18
% 5.52/5.71  # Proof object clause conjectures      : 15
% 5.52/5.71  # Proof object formula conjectures     : 3
% 5.52/5.71  # Proof object initial clauses used    : 21
% 5.52/5.71  # Proof object initial formulas used   : 18
% 5.52/5.71  # Proof object generating inferences   : 35
% 5.52/5.71  # Proof object simplifying inferences  : 90
% 5.52/5.71  # Training examples: 0 positive, 0 negative
% 5.52/5.71  # Parsed axioms                        : 20
% 5.52/5.71  # Removed by relevancy pruning/SinE    : 0
% 5.52/5.71  # Initial clauses                      : 24
% 5.52/5.71  # Removed in clause preprocessing      : 2
% 5.52/5.71  # Initial clauses in saturation        : 22
% 5.52/5.71  # Processed clauses                    : 6559
% 5.52/5.71  # ...of these trivial                  : 3292
% 5.52/5.71  # ...subsumed                          : 931
% 5.52/5.71  # ...remaining for further processing  : 2336
% 5.52/5.71  # Other redundant clauses eliminated   : 0
% 5.52/5.71  # Clauses deleted for lack of memory   : 0
% 5.52/5.71  # Backward-subsumed                    : 1
% 5.52/5.71  # Backward-rewritten                   : 832
% 5.52/5.71  # Generated clauses                    : 428745
% 5.52/5.71  # ...of the previous two non-trivial   : 189148
% 5.52/5.71  # Contextual simplify-reflections      : 0
% 5.52/5.71  # Paramodulations                      : 428738
% 5.52/5.71  # Factorizations                       : 0
% 5.52/5.71  # Equation resolutions                 : 7
% 5.52/5.71  # Propositional unsat checks           : 0
% 5.52/5.71  #    Propositional check models        : 0
% 5.52/5.71  #    Propositional check unsatisfiable : 0
% 5.52/5.71  #    Propositional clauses             : 0
% 5.52/5.71  #    Propositional clauses after purity: 0
% 5.52/5.71  #    Propositional unsat core size     : 0
% 5.52/5.71  #    Propositional preprocessing time  : 0.000
% 5.52/5.71  #    Propositional encoding time       : 0.000
% 5.52/5.71  #    Propositional solver time         : 0.000
% 5.52/5.71  #    Success case prop preproc time    : 0.000
% 5.52/5.71  #    Success case prop encoding time   : 0.000
% 5.52/5.71  #    Success case prop solver time     : 0.000
% 5.52/5.71  # Current number of processed clauses  : 1482
% 5.52/5.71  #    Positive orientable unit clauses  : 1372
% 5.52/5.71  #    Positive unorientable unit clauses: 17
% 5.52/5.71  #    Negative unit clauses             : 1
% 5.52/5.71  #    Non-unit-clauses                  : 92
% 5.52/5.71  # Current number of unprocessed clauses: 181332
% 5.52/5.71  # ...number of literals in the above   : 186082
% 5.52/5.71  # Current number of archived formulas  : 0
% 5.52/5.71  # Current number of archived clauses   : 856
% 5.52/5.71  # Clause-clause subsumption calls (NU) : 2580
% 5.52/5.71  # Rec. Clause-clause subsumption calls : 2580
% 5.52/5.71  # Non-unit clause-clause subsumptions  : 866
% 5.52/5.71  # Unit Clause-clause subsumption calls : 2033
% 5.52/5.71  # Rewrite failures with RHS unbound    : 0
% 5.52/5.71  # BW rewrite match attempts            : 16429
% 5.52/5.71  # BW rewrite match successes           : 1796
% 5.52/5.71  # Condensation attempts                : 0
% 5.52/5.71  # Condensation successes               : 0
% 5.52/5.71  # Termbank termtop insertions          : 8373738
% 5.55/5.73  
% 5.55/5.73  # -------------------------------------------------
% 5.55/5.73  # User time                : 5.192 s
% 5.55/5.73  # System time              : 0.176 s
% 5.55/5.73  # Total time               : 5.367 s
% 5.55/5.73  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
