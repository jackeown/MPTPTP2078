%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:24 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 775 expanded)
%              Number of clauses        :   51 ( 361 expanded)
%              Number of leaves         :   15 ( 184 expanded)
%              Depth                    :   15
%              Number of atoms          :  165 (1621 expanded)
%              Number of equality atoms :  105 (1306 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(t128_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
    <=> ( X1 = X3
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(t63_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k3_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
     => r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t129_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))
    <=> ( r2_hidden(X1,X3)
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(t12_zfmisc_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(fc1_zfmisc_1,axiom,(
    ! [X1,X2] : ~ v1_xboole_0(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_zfmisc_1)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_16,plain,(
    ! [X43,X44] :
      ( k1_mcart_1(k4_tarski(X43,X44)) = X43
      & k2_mcart_1(k4_tarski(X43,X44)) = X44 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_17,negated_conjecture,
    ( esk2_0 = k4_tarski(esk3_0,esk4_0)
    & ( esk2_0 = k1_mcart_1(esk2_0)
      | esk2_0 = k2_mcart_1(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_18,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( esk2_0 = k4_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X31,X32,X33] :
      ( k2_zfmisc_1(k1_tarski(X31),k2_tarski(X32,X33)) = k2_tarski(k4_tarski(X31,X32),k4_tarski(X31,X33))
      & k2_zfmisc_1(k2_tarski(X31,X32),k1_tarski(X33)) = k2_tarski(k4_tarski(X31,X33),k4_tarski(X32,X33)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_22,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( esk2_0 = k1_mcart_1(esk2_0)
    | esk2_0 = k2_mcart_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_25,plain,(
    ! [X12,X13,X14] :
      ( ( ~ r1_tarski(X12,k2_tarski(X13,X14))
        | X12 = k1_xboole_0
        | X12 = k1_tarski(X13)
        | X12 = k1_tarski(X14)
        | X12 = k2_tarski(X13,X14) )
      & ( X12 != k1_xboole_0
        | r1_tarski(X12,k2_tarski(X13,X14)) )
      & ( X12 != k1_tarski(X13)
        | r1_tarski(X12,k2_tarski(X13,X14)) )
      & ( X12 != k1_tarski(X14)
        | r1_tarski(X12,k2_tarski(X13,X14)) )
      & ( X12 != k2_tarski(X13,X14)
        | r1_tarski(X12,k2_tarski(X13,X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_26,plain,(
    ! [X17,X18,X19,X20] :
      ( ( X17 = X19
        | ~ r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(k1_tarski(X19),X20)) )
      & ( r2_hidden(X18,X20)
        | ~ r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(k1_tarski(X19),X20)) )
      & ( X17 != X19
        | ~ r2_hidden(X18,X20)
        | r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(k1_tarski(X19),X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).

fof(c_0_27,plain,(
    ! [X15,X16] :
      ( ( k2_zfmisc_1(X15,X16) != k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_28,plain,(
    ! [X27,X28] :
      ( ( ~ r1_tarski(X27,k2_zfmisc_1(X27,X28))
        | X27 = k1_xboole_0 )
      & ( ~ r1_tarski(X27,k2_zfmisc_1(X28,X27))
        | X27 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X34,X35,X36] :
      ( k3_xboole_0(k2_tarski(X34,X35),X36) != k2_tarski(X34,X35)
      | r2_hidden(X34,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_zfmisc_1])])).

fof(c_0_32,plain,(
    ! [X7,X8] : k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k3_xboole_0(X7,X8) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_33,plain,(
    ! [X6] : k3_xboole_0(X6,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_34,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk2_0
    | esk3_0 = esk2_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k2_tarski(X3,X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | k3_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,negated_conjecture,
    ( esk3_0 = esk2_0
    | esk4_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k2_tarski(X3,X2))
    | X1 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_30])).

cnf(c_0_47,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_tarski(X2,X2),X4)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_30])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_38])).

fof(c_0_49,plain,(
    ! [X21,X22,X23,X24] :
      ( ( r2_hidden(X21,X23)
        | ~ r2_hidden(k4_tarski(X21,X22),k2_zfmisc_1(X23,k1_tarski(X24))) )
      & ( X22 = X24
        | ~ r2_hidden(k4_tarski(X21,X22),k2_zfmisc_1(X23,k1_tarski(X24))) )
      & ( ~ r2_hidden(X21,X23)
        | X22 != X24
        | r2_hidden(k4_tarski(X21,X22),k2_zfmisc_1(X23,k1_tarski(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).

cnf(c_0_50,plain,
    ( k2_tarski(X1,X2) = k1_xboole_0
    | ~ r1_tarski(k2_tarski(X1,X2),k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X3)
    | k4_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k2_tarski(X1,X2),X3)) != k2_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_53,plain,
    ( k2_tarski(X1,X1) = k1_xboole_0
    | ~ r1_tarski(k2_tarski(X1,X1),k2_tarski(k4_tarski(X2,X1),k4_tarski(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( k4_tarski(esk3_0,esk2_0) = esk2_0
    | esk3_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_45])).

cnf(c_0_55,plain,
    ( r1_tarski(k2_tarski(X1,X1),k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_57,plain,(
    ! [X25,X26] : r1_tarski(k1_tarski(X25),k2_tarski(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t12_zfmisc_1])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( k2_tarski(X1,esk3_0) = k1_xboole_0
    | ~ r1_tarski(k2_tarski(X1,esk3_0),k2_tarski(k4_tarski(X1,esk4_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_19])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,k1_xboole_0)
    | k2_tarski(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( k2_tarski(esk2_0,esk2_0) = k1_xboole_0
    | esk3_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_63,negated_conjecture,
    ( esk3_0 = X1
    | ~ r2_hidden(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_19])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_30])).

cnf(c_0_66,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( k2_tarski(esk3_0,esk3_0) = k1_xboole_0
    | ~ r1_tarski(k2_tarski(esk3_0,esk3_0),k2_tarski(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_19])).

cnf(c_0_68,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_69,plain,
    ( r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_30])).

cnf(c_0_70,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( k2_tarski(esk2_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_68]),c_0_68]),c_0_68]),c_0_69])])).

fof(c_0_72,plain,(
    ! [X10,X11] : ~ v1_xboole_0(k4_tarski(X10,X11)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_zfmisc_1])])).

cnf(c_0_73,negated_conjecture,
    ( esk4_0 = X1
    | ~ r2_hidden(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_19])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_71])).

cnf(c_0_75,plain,
    ( ~ v1_xboole_0(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( esk4_0 = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])])).

fof(c_0_77,plain,(
    v1_xboole_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

cnf(c_0_78,plain,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,plain,
    ( v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_76])).

cnf(c_0_81,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_79,c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:29:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S04DN
% 0.12/0.37  # and selection function SelectNewComplex.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.12/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.12/0.37  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.12/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.37  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 0.12/0.37  fof(t128_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 0.12/0.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.12/0.37  fof(t135_zfmisc_1, axiom, ![X1, X2]:((r1_tarski(X1,k2_zfmisc_1(X1,X2))|r1_tarski(X1,k2_zfmisc_1(X2,X1)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 0.12/0.37  fof(t63_zfmisc_1, axiom, ![X1, X2, X3]:(k3_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)=>r2_hidden(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 0.12/0.37  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.37  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.12/0.37  fof(t129_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))<=>(r2_hidden(X1,X3)&X2=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 0.12/0.37  fof(t12_zfmisc_1, axiom, ![X1, X2]:r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 0.12/0.37  fof(fc1_zfmisc_1, axiom, ![X1, X2]:~(v1_xboole_0(k4_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_zfmisc_1)).
% 0.12/0.37  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.12/0.37  fof(c_0_15, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.12/0.37  fof(c_0_16, plain, ![X43, X44]:(k1_mcart_1(k4_tarski(X43,X44))=X43&k2_mcart_1(k4_tarski(X43,X44))=X44), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.12/0.37  fof(c_0_17, negated_conjecture, (esk2_0=k4_tarski(esk3_0,esk4_0)&(esk2_0=k1_mcart_1(esk2_0)|esk2_0=k2_mcart_1(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.12/0.37  cnf(c_0_18, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (esk2_0=k4_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  fof(c_0_20, plain, ![X31, X32, X33]:(k2_zfmisc_1(k1_tarski(X31),k2_tarski(X32,X33))=k2_tarski(k4_tarski(X31,X32),k4_tarski(X31,X33))&k2_zfmisc_1(k2_tarski(X31,X32),k1_tarski(X33))=k2_tarski(k4_tarski(X31,X33),k4_tarski(X32,X33))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.12/0.37  fof(c_0_21, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.37  cnf(c_0_22, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (esk2_0=k1_mcart_1(esk2_0)|esk2_0=k2_mcart_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (k1_mcart_1(esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  fof(c_0_25, plain, ![X12, X13, X14]:((~r1_tarski(X12,k2_tarski(X13,X14))|(X12=k1_xboole_0|X12=k1_tarski(X13)|X12=k1_tarski(X14)|X12=k2_tarski(X13,X14)))&((((X12!=k1_xboole_0|r1_tarski(X12,k2_tarski(X13,X14)))&(X12!=k1_tarski(X13)|r1_tarski(X12,k2_tarski(X13,X14))))&(X12!=k1_tarski(X14)|r1_tarski(X12,k2_tarski(X13,X14))))&(X12!=k2_tarski(X13,X14)|r1_tarski(X12,k2_tarski(X13,X14))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 0.12/0.37  fof(c_0_26, plain, ![X17, X18, X19, X20]:(((X17=X19|~r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(k1_tarski(X19),X20)))&(r2_hidden(X18,X20)|~r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(k1_tarski(X19),X20))))&(X17!=X19|~r2_hidden(X18,X20)|r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(k1_tarski(X19),X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).
% 0.12/0.37  fof(c_0_27, plain, ![X15, X16]:((k2_zfmisc_1(X15,X16)!=k1_xboole_0|(X15=k1_xboole_0|X16=k1_xboole_0))&((X15!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0)&(X16!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.12/0.37  fof(c_0_28, plain, ![X27, X28]:((~r1_tarski(X27,k2_zfmisc_1(X27,X28))|X27=k1_xboole_0)&(~r1_tarski(X27,k2_zfmisc_1(X28,X27))|X27=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).
% 0.12/0.37  cnf(c_0_29, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  fof(c_0_31, plain, ![X34, X35, X36]:(k3_xboole_0(k2_tarski(X34,X35),X36)!=k2_tarski(X34,X35)|r2_hidden(X34,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_zfmisc_1])])).
% 0.12/0.37  fof(c_0_32, plain, ![X7, X8]:k4_xboole_0(X7,k4_xboole_0(X7,X8))=k3_xboole_0(X7,X8), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.37  fof(c_0_33, plain, ![X6]:k3_xboole_0(X6,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (k2_mcart_1(esk2_0)=esk4_0), inference(spm,[status(thm)],[c_0_22, c_0_19])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (k2_mcart_1(esk2_0)=esk2_0|esk3_0=esk2_0), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.37  cnf(c_0_36, plain, (r1_tarski(X1,k2_tarski(X3,X2))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_37, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  cnf(c_0_38, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.37  cnf(c_0_39, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_40, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.37  cnf(c_0_41, plain, (r2_hidden(X1,X3)|k3_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.37  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_43, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.37  cnf(c_0_44, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (esk3_0=esk2_0|esk4_0=esk2_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.12/0.37  cnf(c_0_46, plain, (r1_tarski(X1,k2_tarski(X3,X2))|X1!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_36, c_0_30])).
% 0.12/0.37  cnf(c_0_47, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_tarski(X2,X2),X4))), inference(rw,[status(thm)],[c_0_37, c_0_30])).
% 0.12/0.37  cnf(c_0_48, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_38])).
% 0.12/0.37  fof(c_0_49, plain, ![X21, X22, X23, X24]:(((r2_hidden(X21,X23)|~r2_hidden(k4_tarski(X21,X22),k2_zfmisc_1(X23,k1_tarski(X24))))&(X22=X24|~r2_hidden(k4_tarski(X21,X22),k2_zfmisc_1(X23,k1_tarski(X24)))))&(~r2_hidden(X21,X23)|X22!=X24|r2_hidden(k4_tarski(X21,X22),k2_zfmisc_1(X23,k1_tarski(X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).
% 0.12/0.37  cnf(c_0_50, plain, (k2_tarski(X1,X2)=k1_xboole_0|~r1_tarski(k2_tarski(X1,X2),k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.37  cnf(c_0_51, plain, (r2_hidden(X1,X3)|k4_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k2_tarski(X1,X2),X3))!=k2_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.37  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_43, c_0_42])).
% 0.12/0.37  cnf(c_0_53, plain, (k2_tarski(X1,X1)=k1_xboole_0|~r1_tarski(k2_tarski(X1,X1),k2_tarski(k4_tarski(X2,X1),k4_tarski(X3,X1)))), inference(spm,[status(thm)],[c_0_44, c_0_40])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (k4_tarski(esk3_0,esk2_0)=esk2_0|esk3_0=esk2_0), inference(spm,[status(thm)],[c_0_19, c_0_45])).
% 0.12/0.37  cnf(c_0_55, plain, (r1_tarski(k2_tarski(X1,X1),k2_tarski(X2,X1))), inference(er,[status(thm)],[c_0_46])).
% 0.12/0.37  cnf(c_0_56, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.12/0.37  fof(c_0_57, plain, ![X25, X26]:r1_tarski(k1_tarski(X25),k2_tarski(X25,X26)), inference(variable_rename,[status(thm)],[t12_zfmisc_1])).
% 0.12/0.37  cnf(c_0_58, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.37  cnf(c_0_59, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.37  cnf(c_0_60, negated_conjecture, (k2_tarski(X1,esk3_0)=k1_xboole_0|~r1_tarski(k2_tarski(X1,esk3_0),k2_tarski(k4_tarski(X1,esk4_0),esk2_0))), inference(spm,[status(thm)],[c_0_50, c_0_19])).
% 0.12/0.37  cnf(c_0_61, plain, (r2_hidden(X1,k1_xboole_0)|k2_tarski(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.12/0.37  cnf(c_0_62, negated_conjecture, (k2_tarski(esk2_0,esk2_0)=k1_xboole_0|esk3_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.12/0.37  cnf(c_0_63, negated_conjecture, (esk3_0=X1|~r2_hidden(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_19])).
% 0.12/0.37  cnf(c_0_64, plain, (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.12/0.37  cnf(c_0_65, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k2_tarski(X2,X2)))), inference(rw,[status(thm)],[c_0_58, c_0_30])).
% 0.12/0.37  cnf(c_0_66, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_59])).
% 0.12/0.37  cnf(c_0_67, negated_conjecture, (k2_tarski(esk3_0,esk3_0)=k1_xboole_0|~r1_tarski(k2_tarski(esk3_0,esk3_0),k2_tarski(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_60, c_0_19])).
% 0.12/0.37  cnf(c_0_68, negated_conjecture, (esk3_0=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.12/0.37  cnf(c_0_69, plain, (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_64, c_0_30])).
% 0.12/0.37  cnf(c_0_70, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.12/0.37  cnf(c_0_71, negated_conjecture, (k2_tarski(esk2_0,esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68]), c_0_68]), c_0_68]), c_0_68]), c_0_69])])).
% 0.12/0.37  fof(c_0_72, plain, ![X10, X11]:~v1_xboole_0(k4_tarski(X10,X11)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_zfmisc_1])])).
% 0.12/0.37  cnf(c_0_73, negated_conjecture, (esk4_0=X1|~r2_hidden(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_70, c_0_19])).
% 0.12/0.37  cnf(c_0_74, negated_conjecture, (r2_hidden(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_61, c_0_71])).
% 0.12/0.37  cnf(c_0_75, plain, (~v1_xboole_0(k4_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.12/0.37  cnf(c_0_76, negated_conjecture, (esk4_0=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74])])).
% 0.12/0.37  fof(c_0_77, plain, v1_xboole_0(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.12/0.37  cnf(c_0_78, plain, (~v1_xboole_0(esk4_0)), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.12/0.37  cnf(c_0_79, plain, (v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.12/0.37  cnf(c_0_80, negated_conjecture, (~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_78, c_0_76])).
% 0.12/0.37  cnf(c_0_81, plain, ($false), inference(sr,[status(thm)],[c_0_79, c_0_80]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 82
% 0.12/0.37  # Proof object clause steps            : 51
% 0.12/0.37  # Proof object formula steps           : 31
% 0.12/0.37  # Proof object conjectures             : 20
% 0.12/0.37  # Proof object clause conjectures      : 17
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 19
% 0.12/0.37  # Proof object initial formulas used   : 15
% 0.12/0.37  # Proof object generating inferences   : 17
% 0.12/0.37  # Proof object simplifying inferences  : 24
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 19
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 36
% 0.12/0.37  # Removed in clause preprocessing      : 2
% 0.12/0.37  # Initial clauses in saturation        : 34
% 0.12/0.37  # Processed clauses                    : 197
% 0.12/0.37  # ...of these trivial                  : 1
% 0.12/0.37  # ...subsumed                          : 57
% 0.12/0.37  # ...remaining for further processing  : 139
% 0.12/0.37  # Other redundant clauses eliminated   : 8
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 3
% 0.12/0.37  # Backward-rewritten                   : 83
% 0.12/0.37  # Generated clauses                    : 237
% 0.12/0.37  # ...of the previous two non-trivial   : 287
% 0.12/0.37  # Contextual simplify-reflections      : 1
% 0.12/0.37  # Paramodulations                      : 228
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 8
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 12
% 0.12/0.37  #    Positive orientable unit clauses  : 2
% 0.12/0.37  #    Positive unorientable unit clauses: 1
% 0.12/0.37  #    Negative unit clauses             : 3
% 0.12/0.37  #    Non-unit-clauses                  : 6
% 0.12/0.37  # Current number of unprocessed clauses: 155
% 0.12/0.37  # ...number of literals in the above   : 319
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 121
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 818
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 664
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 59
% 0.12/0.37  # Unit Clause-clause subsumption calls : 11
% 0.12/0.37  # Rewrite failures with RHS unbound    : 5
% 0.12/0.37  # BW rewrite match attempts            : 76
% 0.12/0.37  # BW rewrite match successes           : 67
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 5008
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.035 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.041 s
% 0.12/0.37  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
