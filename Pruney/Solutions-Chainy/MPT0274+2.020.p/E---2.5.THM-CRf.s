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
% DateTime   : Thu Dec  3 10:42:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 726 expanded)
%              Number of clauses        :   69 ( 325 expanded)
%              Number of leaves         :   20 ( 197 expanded)
%              Depth                    :   17
%              Number of atoms          :  189 (1018 expanded)
%              Number of equality atoms :   57 ( 600 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t83_enumset1,axiom,(
    ! [X1,X2] : k3_enumset1(X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t90_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t81_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t82_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t72_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(t57_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X3,X2)
        & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t12_zfmisc_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(t87_enumset1,axiom,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(c_0_20,plain,(
    ! [X28,X29] : k3_xboole_0(X28,X29) = k5_xboole_0(k5_xboole_0(X28,X29),k2_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_21,plain,(
    ! [X39,X40] : k3_tarski(k2_tarski(X39,X40)) = k2_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X36,X37] : k3_enumset1(X36,X36,X36,X36,X37) = k2_tarski(X36,X37) ),
    inference(variable_rename,[status(thm)],[t83_enumset1])).

fof(c_0_23,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k3_xboole_0(X12,X13)) = k4_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X32,X33] : k2_xboole_0(X32,X33) = k5_xboole_0(X32,k4_xboole_0(X33,X32)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_28,plain,(
    ! [X23,X24] : r1_xboole_0(k4_xboole_0(X23,k3_xboole_0(X23,X24)),X24) ),
    inference(variable_rename,[status(thm)],[t90_xboole_1])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X25,X26,X27] : k5_xboole_0(k5_xboole_0(X25,X26),X27) = k5_xboole_0(X25,k5_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_33,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_25]),c_0_26])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_37,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_xboole_0(X16,k4_xboole_0(X17,X18))
      | r1_xboole_0(X17,k4_xboole_0(X16,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).

fof(c_0_38,plain,(
    ! [X19,X20] : r1_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X20,X19)) ),
    inference(variable_rename,[status(thm)],[t82_xboole_1])).

fof(c_0_39,plain,(
    ! [X21,X22] :
      ( ( ~ r1_xboole_0(X21,X22)
        | k4_xboole_0(X21,X22) = X21 )
      & ( k4_xboole_0(X21,X22) != X21
        | r1_xboole_0(X21,X22) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_40,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))),X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_30])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X2,X1))))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X2,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_35]),c_0_36]),c_0_41])).

fof(c_0_46,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,k2_xboole_0(X10,X11))
      | r1_tarski(k4_xboole_0(X9,X10),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_47,plain,(
    ! [X14,X15] : r1_tarski(X14,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_52,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,k4_xboole_0(X8,X7))
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_25]),c_0_26])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_25]),c_0_26])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_53])).

cnf(c_0_58,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_35])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_55,c_0_35])).

fof(c_0_60,plain,(
    ! [X34,X35] : k2_tarski(X34,X35) = k2_tarski(X35,X34) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_61,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
      <=> ( ~ r2_hidden(X1,X3)
          & ~ r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t72_zfmisc_1])).

fof(c_0_62,plain,(
    ! [X46,X47,X48] :
      ( r2_hidden(X46,X47)
      | r2_hidden(X48,X47)
      | r1_xboole_0(k2_tarski(X46,X48),X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_zfmisc_1])])])).

fof(c_0_63,plain,(
    ! [X43,X44,X45] :
      ( ( r2_hidden(X43,X45)
        | ~ r1_tarski(k2_tarski(X43,X44),X45) )
      & ( r2_hidden(X44,X45)
        | ~ r1_tarski(k2_tarski(X43,X44),X45) )
      & ( ~ r2_hidden(X43,X45)
        | ~ r2_hidden(X44,X45)
        | r1_tarski(k2_tarski(X43,X44),X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_67,negated_conjecture,
    ( ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_tarski(esk1_0,esk2_0)
      | r2_hidden(esk1_0,esk3_0)
      | r2_hidden(esk2_0,esk3_0) )
    & ( ~ r2_hidden(esk1_0,esk3_0)
      | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k2_tarski(esk1_0,esk2_0) )
    & ( ~ r2_hidden(esk2_0,esk3_0)
      | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k2_tarski(esk1_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_61])])])])])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r1_xboole_0(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_70,plain,(
    ! [X41,X42] : r1_tarski(k1_tarski(X41),k2_tarski(X41,X42)) ),
    inference(variable_rename,[status(thm)],[t12_zfmisc_1])).

fof(c_0_71,plain,(
    ! [X38] : k3_enumset1(X38,X38,X38,X38,X38) = k1_tarski(X38) ),
    inference(variable_rename,[status(thm)],[t87_enumset1])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65])])).

fof(c_0_73,plain,(
    ! [X4,X5,X6] :
      ( ( ~ r2_hidden(X4,X5)
        | ~ r2_hidden(X4,X6)
        | ~ r2_hidden(X4,k5_xboole_0(X5,X6)) )
      & ( r2_hidden(X4,X5)
        | r2_hidden(X4,X6)
        | ~ r2_hidden(X4,k5_xboole_0(X5,X6)) )
      & ( ~ r2_hidden(X4,X5)
        | r2_hidden(X4,X6)
        | r2_hidden(X4,k5_xboole_0(X5,X6)) )
      & ( ~ r2_hidden(X4,X6)
        | r2_hidden(X4,X5)
        | r2_hidden(X4,k5_xboole_0(X5,X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_74,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_26]),c_0_26])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r2_hidden(esk2_0,esk3_0)
    | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( r2_hidden(X3,X2)
    | r2_hidden(X1,X2)
    | r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_26])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k3_enumset1(X3,X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[c_0_69,c_0_26])).

cnf(c_0_79,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_80,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X1)))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_57])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_57,c_0_72])).

cnf(c_0_83,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_74]),c_0_35])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[c_0_75,c_0_26])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k2_tarski(esk1_0,esk2_0)
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r2_hidden(esk2_0,esk3_0)
    | k4_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0) != k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_26]),c_0_26])).

cnf(c_0_88,plain,
    ( k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),X3) = k3_enumset1(X1,X1,X1,X1,X2)
    | r2_hidden(X1,X3)
    | r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_77])).

cnf(c_0_89,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k2_tarski(esk1_0,esk2_0)
    | ~ r2_hidden(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),k4_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_59])).

cnf(c_0_91,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_26])).

cnf(c_0_92,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_72]),c_0_82])).

cnf(c_0_93,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k4_xboole_0(X3,k3_enumset1(X1,X1,X1,X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_59])).

cnf(c_0_95,negated_conjecture,
    ( k4_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_26]),c_0_26])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r2_hidden(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( k4_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)
    | ~ r2_hidden(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_26]),c_0_26])).

cnf(c_0_98,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X1)))
    | ~ r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_90])).

cnf(c_0_99,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_91])).

cnf(c_0_100,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_45])).

cnf(c_0_101,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),X3))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_102,negated_conjecture,
    ( k4_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0) = k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97])).

cnf(c_0_103,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_74]),c_0_99])])).

cnf(c_0_104,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_99])])).

cnf(c_0_106,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X1))) ),
    inference(spm,[status(thm)],[c_0_103,c_0_74])).

cnf(c_0_107,negated_conjecture,
    ( k4_xboole_0(esk3_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_104,c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_96,c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_108])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:40:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.39  # and selection function SelectNegativeLiterals.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.20/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.39  fof(t83_enumset1, axiom, ![X1, X2]:k3_enumset1(X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_enumset1)).
% 0.20/0.39  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.20/0.39  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.39  fof(t90_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_xboole_1)).
% 0.20/0.39  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.39  fof(t81_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 0.20/0.39  fof(t82_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 0.20/0.39  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.39  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.20/0.39  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.39  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 0.20/0.39  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.39  fof(t72_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 0.20/0.39  fof(t57_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X2))&~(r2_hidden(X3,X2)))&~(r1_xboole_0(k2_tarski(X1,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 0.20/0.39  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.20/0.39  fof(t12_zfmisc_1, axiom, ![X1, X2]:r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 0.20/0.39  fof(t87_enumset1, axiom, ![X1]:k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_enumset1)).
% 0.20/0.39  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.20/0.39  fof(c_0_20, plain, ![X28, X29]:k3_xboole_0(X28,X29)=k5_xboole_0(k5_xboole_0(X28,X29),k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.20/0.39  fof(c_0_21, plain, ![X39, X40]:k3_tarski(k2_tarski(X39,X40))=k2_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.39  fof(c_0_22, plain, ![X36, X37]:k3_enumset1(X36,X36,X36,X36,X37)=k2_tarski(X36,X37), inference(variable_rename,[status(thm)],[t83_enumset1])).
% 0.20/0.39  fof(c_0_23, plain, ![X12, X13]:k4_xboole_0(X12,k3_xboole_0(X12,X13))=k4_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.20/0.39  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_25, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  fof(c_0_27, plain, ![X32, X33]:k2_xboole_0(X32,X33)=k5_xboole_0(X32,k4_xboole_0(X33,X32)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.39  fof(c_0_28, plain, ![X23, X24]:r1_xboole_0(k4_xboole_0(X23,k3_xboole_0(X23,X24)),X24), inference(variable_rename,[status(thm)],[t90_xboole_1])).
% 0.20/0.39  cnf(c_0_29, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.20/0.39  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  fof(c_0_32, plain, ![X25, X26, X27]:k5_xboole_0(k5_xboole_0(X25,X26),X27)=k5_xboole_0(X25,k5_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.39  cnf(c_0_33, plain, (r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_34, plain, (k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.39  cnf(c_0_35, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_25]), c_0_26])).
% 0.20/0.39  cnf(c_0_36, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.39  fof(c_0_37, plain, ![X16, X17, X18]:(~r1_xboole_0(X16,k4_xboole_0(X17,X18))|r1_xboole_0(X17,k4_xboole_0(X16,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).
% 0.20/0.39  fof(c_0_38, plain, ![X19, X20]:r1_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X20,X19)), inference(variable_rename,[status(thm)],[t82_xboole_1])).
% 0.20/0.39  fof(c_0_39, plain, ![X21, X22]:((~r1_xboole_0(X21,X22)|k4_xboole_0(X21,X22)=X21)&(k4_xboole_0(X21,X22)!=X21|r1_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.39  cnf(c_0_40, plain, (r1_xboole_0(k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))),X2)), inference(rw,[status(thm)],[c_0_33, c_0_30])).
% 0.20/0.39  cnf(c_0_41, plain, (k4_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X2,X1)))))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.20/0.39  cnf(c_0_42, plain, (r1_xboole_0(X2,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.39  cnf(c_0_43, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.39  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.39  cnf(c_0_45, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_35]), c_0_36]), c_0_41])).
% 0.20/0.39  fof(c_0_46, plain, ![X9, X10, X11]:(~r1_tarski(X9,k2_xboole_0(X10,X11))|r1_tarski(k4_xboole_0(X9,X10),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.20/0.39  fof(c_0_47, plain, ![X14, X15]:r1_tarski(X14,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.39  cnf(c_0_48, plain, (r1_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X2))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.39  cnf(c_0_49, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.39  cnf(c_0_50, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.39  cnf(c_0_51, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.39  fof(c_0_52, plain, ![X7, X8]:(~r1_tarski(X7,k4_xboole_0(X8,X7))|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 0.20/0.39  cnf(c_0_53, plain, (r1_xboole_0(X1,k4_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.39  cnf(c_0_54, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_25]), c_0_26])).
% 0.20/0.39  cnf(c_0_55, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_25]), c_0_26])).
% 0.20/0.39  cnf(c_0_56, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.39  cnf(c_0_57, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(spm,[status(thm)],[c_0_44, c_0_53])).
% 0.20/0.39  cnf(c_0_58, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_54, c_0_35])).
% 0.20/0.39  cnf(c_0_59, plain, (r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_55, c_0_35])).
% 0.20/0.39  fof(c_0_60, plain, ![X34, X35]:k2_tarski(X34,X35)=k2_tarski(X35,X34), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.39  fof(c_0_61, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3))))), inference(assume_negation,[status(cth)],[t72_zfmisc_1])).
% 0.20/0.39  fof(c_0_62, plain, ![X46, X47, X48]:(r2_hidden(X46,X47)|r2_hidden(X48,X47)|r1_xboole_0(k2_tarski(X46,X48),X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_zfmisc_1])])])).
% 0.20/0.39  fof(c_0_63, plain, ![X43, X44, X45]:(((r2_hidden(X43,X45)|~r1_tarski(k2_tarski(X43,X44),X45))&(r2_hidden(X44,X45)|~r1_tarski(k2_tarski(X43,X44),X45)))&(~r2_hidden(X43,X45)|~r2_hidden(X44,X45)|r1_tarski(k2_tarski(X43,X44),X45))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.20/0.39  cnf(c_0_64, plain, (k4_xboole_0(X1,X1)=k1_xboole_0|~r1_tarski(k4_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.39  cnf(c_0_65, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.39  cnf(c_0_66, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.39  fof(c_0_67, negated_conjecture, ((k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)!=k2_tarski(esk1_0,esk2_0)|(r2_hidden(esk1_0,esk3_0)|r2_hidden(esk2_0,esk3_0)))&((~r2_hidden(esk1_0,esk3_0)|k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k2_tarski(esk1_0,esk2_0))&(~r2_hidden(esk2_0,esk3_0)|k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k2_tarski(esk1_0,esk2_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_61])])])])])).
% 0.20/0.39  cnf(c_0_68, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r1_xboole_0(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.39  cnf(c_0_69, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.39  fof(c_0_70, plain, ![X41, X42]:r1_tarski(k1_tarski(X41),k2_tarski(X41,X42)), inference(variable_rename,[status(thm)],[t12_zfmisc_1])).
% 0.20/0.39  fof(c_0_71, plain, ![X38]:k3_enumset1(X38,X38,X38,X38,X38)=k1_tarski(X38), inference(variable_rename,[status(thm)],[t87_enumset1])).
% 0.20/0.39  cnf(c_0_72, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65])])).
% 0.20/0.39  fof(c_0_73, plain, ![X4, X5, X6]:(((~r2_hidden(X4,X5)|~r2_hidden(X4,X6)|~r2_hidden(X4,k5_xboole_0(X5,X6)))&(r2_hidden(X4,X5)|r2_hidden(X4,X6)|~r2_hidden(X4,k5_xboole_0(X5,X6))))&((~r2_hidden(X4,X5)|r2_hidden(X4,X6)|r2_hidden(X4,k5_xboole_0(X5,X6)))&(~r2_hidden(X4,X6)|r2_hidden(X4,X5)|r2_hidden(X4,k5_xboole_0(X5,X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.20/0.39  cnf(c_0_74, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_26]), c_0_26])).
% 0.20/0.39  cnf(c_0_75, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.39  cnf(c_0_76, negated_conjecture, (r2_hidden(esk1_0,esk3_0)|r2_hidden(esk2_0,esk3_0)|k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)!=k2_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.39  cnf(c_0_77, plain, (r2_hidden(X3,X2)|r2_hidden(X1,X2)|r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[c_0_68, c_0_26])).
% 0.20/0.39  cnf(c_0_78, plain, (r2_hidden(X1,X2)|~r1_tarski(k3_enumset1(X3,X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[c_0_69, c_0_26])).
% 0.20/0.39  cnf(c_0_79, plain, (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.39  cnf(c_0_80, plain, (k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.39  cnf(c_0_81, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X1)))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_57])).
% 0.20/0.39  cnf(c_0_82, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_57, c_0_72])).
% 0.20/0.39  cnf(c_0_83, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.39  cnf(c_0_84, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_74]), c_0_35])).
% 0.20/0.39  cnf(c_0_85, plain, (r2_hidden(X1,X2)|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[c_0_75, c_0_26])).
% 0.20/0.39  cnf(c_0_86, negated_conjecture, (k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k2_tarski(esk1_0,esk2_0)|~r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.39  cnf(c_0_87, negated_conjecture, (r2_hidden(esk1_0,esk3_0)|r2_hidden(esk2_0,esk3_0)|k4_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)!=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_26]), c_0_26])).
% 0.20/0.39  cnf(c_0_88, plain, (k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),X3)=k3_enumset1(X1,X1,X1,X1,X2)|r2_hidden(X1,X3)|r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_44, c_0_77])).
% 0.20/0.39  cnf(c_0_89, negated_conjecture, (k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k2_tarski(esk1_0,esk2_0)|~r2_hidden(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.39  cnf(c_0_90, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X1),k4_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X1))))), inference(spm,[status(thm)],[c_0_78, c_0_59])).
% 0.20/0.39  cnf(c_0_91, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80]), c_0_26])).
% 0.20/0.39  cnf(c_0_92, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_72]), c_0_82])).
% 0.20/0.39  cnf(c_0_93, plain, (~r2_hidden(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))|~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.39  cnf(c_0_94, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k4_xboole_0(X3,k3_enumset1(X1,X1,X1,X1,X2))))), inference(spm,[status(thm)],[c_0_85, c_0_59])).
% 0.20/0.39  cnf(c_0_95, negated_conjecture, (k4_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|~r2_hidden(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_26]), c_0_26])).
% 0.20/0.39  cnf(c_0_96, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r2_hidden(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.20/0.39  cnf(c_0_97, negated_conjecture, (k4_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)|~r2_hidden(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_26]), c_0_26])).
% 0.20/0.39  cnf(c_0_98, plain, (~r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X1)))|~r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X1))), inference(spm,[status(thm)],[c_0_83, c_0_90])).
% 0.20/0.39  cnf(c_0_99, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_85, c_0_91])).
% 0.20/0.39  cnf(c_0_100, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_92, c_0_45])).
% 0.20/0.39  cnf(c_0_101, plain, (~r2_hidden(X1,k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),X3))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.20/0.39  cnf(c_0_102, negated_conjecture, (k4_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)=k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97])).
% 0.20/0.39  cnf(c_0_103, plain, (~r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_74]), c_0_99])])).
% 0.20/0.39  cnf(c_0_104, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_44, c_0_100])).
% 0.20/0.39  cnf(c_0_105, negated_conjecture, (~r2_hidden(esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_99])])).
% 0.20/0.39  cnf(c_0_106, plain, (~r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X1)))), inference(spm,[status(thm)],[c_0_103, c_0_74])).
% 0.20/0.39  cnf(c_0_107, negated_conjecture, (k4_xboole_0(esk3_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))=esk3_0), inference(spm,[status(thm)],[c_0_104, c_0_102])).
% 0.20/0.39  cnf(c_0_108, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(sr,[status(thm)],[c_0_96, c_0_105])).
% 0.20/0.39  cnf(c_0_109, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_108])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 110
% 0.20/0.39  # Proof object clause steps            : 69
% 0.20/0.39  # Proof object formula steps           : 41
% 0.20/0.39  # Proof object conjectures             : 15
% 0.20/0.39  # Proof object clause conjectures      : 12
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 23
% 0.20/0.39  # Proof object initial formulas used   : 20
% 0.20/0.39  # Proof object generating inferences   : 24
% 0.20/0.39  # Proof object simplifying inferences  : 44
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 21
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 29
% 0.20/0.39  # Removed in clause preprocessing      : 4
% 0.20/0.39  # Initial clauses in saturation        : 25
% 0.20/0.39  # Processed clauses                    : 475
% 0.20/0.39  # ...of these trivial                  : 60
% 0.20/0.39  # ...subsumed                          : 255
% 0.20/0.39  # ...remaining for further processing  : 160
% 0.20/0.39  # Other redundant clauses eliminated   : 1
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 1
% 0.20/0.39  # Backward-rewritten                   : 13
% 0.20/0.39  # Generated clauses                    : 1576
% 0.20/0.39  # ...of the previous two non-trivial   : 1087
% 0.20/0.39  # Contextual simplify-reflections      : 1
% 0.20/0.39  # Paramodulations                      : 1574
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 1
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 120
% 0.20/0.39  #    Positive orientable unit clauses  : 48
% 0.20/0.39  #    Positive unorientable unit clauses: 3
% 0.20/0.39  #    Negative unit clauses             : 9
% 0.20/0.39  #    Non-unit-clauses                  : 60
% 0.20/0.39  # Current number of unprocessed clauses: 620
% 0.20/0.39  # ...number of literals in the above   : 1140
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 44
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 963
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 719
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 163
% 0.20/0.39  # Unit Clause-clause subsumption calls : 105
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 126
% 0.20/0.39  # BW rewrite match successes           : 36
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 19942
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.050 s
% 0.20/0.40  # System time              : 0.006 s
% 0.20/0.40  # Total time               : 0.056 s
% 0.20/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
