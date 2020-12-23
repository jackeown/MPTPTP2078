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
% DateTime   : Thu Dec  3 10:37:47 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 219 expanded)
%              Number of clauses        :   44 ( 107 expanded)
%              Number of leaves         :    9 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  154 ( 503 expanded)
%              Number of equality atoms :   71 ( 277 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t82_enumset1,axiom,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(t20_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & ! [X4] :
            ( ( r1_tarski(X4,X2)
              & r1_tarski(X4,X3) )
           => r1_tarski(X4,X1) ) )
     => X1 = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t17_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(t6_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(c_0_9,plain,(
    ! [X17,X18] :
      ( ( ~ r1_tarski(X17,k1_tarski(X18))
        | X17 = k1_xboole_0
        | X17 = k1_tarski(X18) )
      & ( X17 != k1_xboole_0
        | r1_tarski(X17,k1_tarski(X18)) )
      & ( X17 != k1_tarski(X18)
        | r1_tarski(X17,k1_tarski(X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_10,plain,(
    ! [X16] : k2_enumset1(X16,X16,X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t82_enumset1])).

fof(c_0_11,plain,(
    ! [X9,X10,X11] :
      ( ( r1_tarski(esk1_3(X9,X10,X11),X10)
        | ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X9,X11)
        | X9 = k3_xboole_0(X10,X11) )
      & ( r1_tarski(esk1_3(X9,X10,X11),X11)
        | ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X9,X11)
        | X9 = k3_xboole_0(X10,X11) )
      & ( ~ r1_tarski(esk1_3(X9,X10,X11),X9)
        | ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X9,X11)
        | X9 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).

fof(c_0_12,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(esk1_3(X1,X2,X3),X3)
    | X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r1_tarski(esk1_3(X1,X2,X3),X2)
    | X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X5,X6] :
      ( ( ~ r1_xboole_0(X5,X6)
        | k3_xboole_0(X5,X6) = k1_xboole_0 )
      & ( k3_xboole_0(X5,X6) != k1_xboole_0
        | r1_xboole_0(X5,X6) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_20,plain,
    ( X1 = k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | r1_tarski(esk1_3(X1,X2,X3),X3)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( X1 = k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | r1_tarski(esk1_3(X1,X2,X3),X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) = k1_xboole_0
    | r1_tarski(esk1_3(k1_xboole_0,X1,k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X2,X2,X2,X2))
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) = k1_xboole_0
    | r1_tarski(esk1_3(k1_xboole_0,X1,k2_enumset1(X2,X2,X2,X2)),X1)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) = k1_xboole_0
    | r1_tarski(esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X2,X2,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) = k1_xboole_0
    | r1_tarski(esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_14]),c_0_14])).

cnf(c_0_31,plain,
    ( r1_tarski(esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X2,X2,X2,X2))
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( r1_tarski(esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X1,X1,X1,X1))
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_29])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | k2_enumset1(X2,X2,X2,X2) != k1_xboole_0
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(ef,[status(thm)],[c_0_30])).

fof(c_0_34,plain,(
    ! [X7,X8] :
      ( ( k4_xboole_0(X7,X8) != k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | k4_xboole_0(X7,X8) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_35,plain,(
    ! [X13] : k4_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1,X2] :
        ( X1 != X2
       => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    inference(assume_negation,[status(cth)],[t17_zfmisc_1])).

cnf(c_0_37,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(esk1_3(X1,X2,X3),X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(X2,X2,X2,X2)
    | esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(X1,X1,X1,X1)
    | esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_32])).

cnf(c_0_40,plain,
    ( esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))
    | k2_enumset1(X1,X1,X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_44,negated_conjecture,
    ( esk2_0 != esk3_0
    & ~ r1_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_45,plain,
    ( X1 = k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_16])).

cnf(c_0_46,plain,
    ( esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0
    | k2_enumset1(X1,X1,X1,X1) = k2_enumset1(X2,X2,X2,X2)
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_16])).

fof(c_0_49,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(k1_tarski(X19),k1_tarski(X20))
      | X19 = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) = k1_xboole_0
    | k2_enumset1(X1,X1,X1,X1) = k2_enumset1(X2,X2,X2,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_21]),c_0_21])]),c_0_48])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_14]),c_0_14])).

cnf(c_0_54,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k2_enumset1(X2,X2,X2,X2)
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_51])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_14]),c_0_14])).

cnf(c_0_57,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))
    | X1 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_14]),c_0_14])).

cnf(c_0_59,negated_conjecture,
    ( esk2_0 = X1
    | ~ r1_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.21/0.49  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.49  #
% 0.21/0.49  # Preprocessing time       : 0.027 s
% 0.21/0.49  # Presaturation interreduction done
% 0.21/0.49  
% 0.21/0.49  # Proof found!
% 0.21/0.49  # SZS status Theorem
% 0.21/0.49  # SZS output start CNFRefutation
% 0.21/0.49  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.21/0.49  fof(t82_enumset1, axiom, ![X1]:k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 0.21/0.49  fof(t20_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&![X4]:((r1_tarski(X4,X2)&r1_tarski(X4,X3))=>r1_tarski(X4,X1)))=>X1=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 0.21/0.49  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.49  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.21/0.49  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.21/0.49  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.21/0.49  fof(t17_zfmisc_1, conjecture, ![X1, X2]:(X1!=X2=>r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 0.21/0.49  fof(t6_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 0.21/0.49  fof(c_0_9, plain, ![X17, X18]:((~r1_tarski(X17,k1_tarski(X18))|(X17=k1_xboole_0|X17=k1_tarski(X18)))&((X17!=k1_xboole_0|r1_tarski(X17,k1_tarski(X18)))&(X17!=k1_tarski(X18)|r1_tarski(X17,k1_tarski(X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.21/0.49  fof(c_0_10, plain, ![X16]:k2_enumset1(X16,X16,X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t82_enumset1])).
% 0.21/0.49  fof(c_0_11, plain, ![X9, X10, X11]:(((r1_tarski(esk1_3(X9,X10,X11),X10)|(~r1_tarski(X9,X10)|~r1_tarski(X9,X11))|X9=k3_xboole_0(X10,X11))&(r1_tarski(esk1_3(X9,X10,X11),X11)|(~r1_tarski(X9,X10)|~r1_tarski(X9,X11))|X9=k3_xboole_0(X10,X11)))&(~r1_tarski(esk1_3(X9,X10,X11),X9)|(~r1_tarski(X9,X10)|~r1_tarski(X9,X11))|X9=k3_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).
% 0.21/0.49  fof(c_0_12, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.49  cnf(c_0_13, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.49  cnf(c_0_14, plain, (k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.49  cnf(c_0_15, plain, (r1_tarski(esk1_3(X1,X2,X3),X3)|X1=k3_xboole_0(X2,X3)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.49  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.49  cnf(c_0_17, plain, (r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.49  cnf(c_0_18, plain, (r1_tarski(esk1_3(X1,X2,X3),X2)|X1=k3_xboole_0(X2,X3)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.49  fof(c_0_19, plain, ![X5, X6]:((~r1_xboole_0(X5,X6)|k3_xboole_0(X5,X6)=k1_xboole_0)&(k3_xboole_0(X5,X6)!=k1_xboole_0|r1_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.21/0.49  cnf(c_0_20, plain, (X1=k4_xboole_0(X2,k4_xboole_0(X2,X3))|r1_tarski(esk1_3(X1,X2,X3),X3)|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.49  cnf(c_0_21, plain, (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_17])).
% 0.21/0.49  cnf(c_0_22, plain, (X1=k4_xboole_0(X2,k4_xboole_0(X2,X3))|r1_tarski(esk1_3(X1,X2,X3),X2)|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_16])).
% 0.21/0.49  cnf(c_0_23, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.49  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))=k1_xboole_0|r1_tarski(esk1_3(k1_xboole_0,X1,k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X2,X2,X2,X2))|~r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.49  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))=k1_xboole_0|r1_tarski(esk1_3(k1_xboole_0,X1,k2_enumset1(X2,X2,X2,X2)),X1)|~r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.21/0.49  cnf(c_0_26, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.49  cnf(c_0_27, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_23, c_0_16])).
% 0.21/0.49  cnf(c_0_28, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))=k1_xboole_0|r1_tarski(esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X2,X2,X2,X2))), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 0.21/0.49  cnf(c_0_29, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))=k1_xboole_0|r1_tarski(esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_25, c_0_21])).
% 0.21/0.49  cnf(c_0_30, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_14]), c_0_14])).
% 0.21/0.49  cnf(c_0_31, plain, (r1_tarski(esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X2,X2,X2,X2))|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.49  cnf(c_0_32, plain, (r1_tarski(esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X1,X1,X1,X1))|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(spm,[status(thm)],[c_0_27, c_0_29])).
% 0.21/0.49  cnf(c_0_33, plain, (X1=k1_xboole_0|k2_enumset1(X2,X2,X2,X2)!=k1_xboole_0|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))), inference(ef,[status(thm)],[c_0_30])).
% 0.21/0.49  fof(c_0_34, plain, ![X7, X8]:((k4_xboole_0(X7,X8)!=k1_xboole_0|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|k4_xboole_0(X7,X8)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.21/0.49  fof(c_0_35, plain, ![X13]:k4_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.21/0.49  fof(c_0_36, negated_conjecture, ~(![X1, X2]:(X1!=X2=>r1_xboole_0(k1_tarski(X1),k1_tarski(X2)))), inference(assume_negation,[status(cth)],[t17_zfmisc_1])).
% 0.21/0.49  cnf(c_0_37, plain, (X1=k3_xboole_0(X2,X3)|~r1_tarski(esk1_3(X1,X2,X3),X1)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.49  cnf(c_0_38, plain, (esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k2_enumset1(X2,X2,X2,X2)|esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k1_xboole_0|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.49  cnf(c_0_39, plain, (esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k2_enumset1(X1,X1,X1,X1)|esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k1_xboole_0|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(spm,[status(thm)],[c_0_30, c_0_32])).
% 0.21/0.49  cnf(c_0_40, plain, (esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k1_xboole_0|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))|k2_enumset1(X1,X1,X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_32])).
% 0.21/0.49  cnf(c_0_41, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.49  cnf(c_0_42, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.49  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.49  fof(c_0_44, negated_conjecture, (esk2_0!=esk3_0&~r1_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 0.21/0.49  cnf(c_0_45, plain, (X1=k4_xboole_0(X2,k4_xboole_0(X2,X3))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_37, c_0_16])).
% 0.21/0.49  cnf(c_0_46, plain, (esk1_3(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k1_xboole_0|k2_enumset1(X1,X1,X1,X1)=k2_enumset1(X2,X2,X2,X2)|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.21/0.49  cnf(c_0_47, plain, (r1_tarski(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42])])).
% 0.21/0.49  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_43, c_0_16])).
% 0.21/0.49  fof(c_0_49, plain, ![X19, X20]:(~r1_tarski(k1_tarski(X19),k1_tarski(X20))|X19=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).
% 0.21/0.49  cnf(c_0_50, negated_conjecture, (~r1_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.49  cnf(c_0_51, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))=k1_xboole_0|k2_enumset1(X1,X1,X1,X1)=k2_enumset1(X2,X2,X2,X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_21]), c_0_21])]), c_0_48])).
% 0.21/0.49  cnf(c_0_52, plain, (X1=X2|~r1_tarski(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.49  cnf(c_0_53, negated_conjecture, (~r1_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_14]), c_0_14])).
% 0.21/0.49  cnf(c_0_54, plain, (k2_enumset1(X1,X1,X1,X1)=k2_enumset1(X2,X2,X2,X2)|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(spm,[status(thm)],[c_0_27, c_0_51])).
% 0.21/0.49  cnf(c_0_55, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.49  cnf(c_0_56, plain, (X1=X2|~r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_14]), c_0_14])).
% 0.21/0.49  cnf(c_0_57, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.49  cnf(c_0_58, plain, (r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))|X1!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_14]), c_0_14])).
% 0.21/0.49  cnf(c_0_59, negated_conjecture, (esk2_0=X1|~r1_tarski(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.49  cnf(c_0_60, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_58])).
% 0.21/0.49  cnf(c_0_61, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.49  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), ['proof']).
% 0.21/0.49  # SZS output end CNFRefutation
% 0.21/0.49  # Proof object total steps             : 63
% 0.21/0.49  # Proof object clause steps            : 44
% 0.21/0.49  # Proof object formula steps           : 19
% 0.21/0.49  # Proof object conjectures             : 9
% 0.21/0.49  # Proof object clause conjectures      : 6
% 0.21/0.49  # Proof object formula conjectures     : 3
% 0.21/0.49  # Proof object initial clauses used    : 15
% 0.21/0.49  # Proof object initial formulas used   : 9
% 0.21/0.49  # Proof object generating inferences   : 17
% 0.21/0.49  # Proof object simplifying inferences  : 24
% 0.21/0.49  # Training examples: 0 positive, 0 negative
% 0.21/0.49  # Parsed axioms                        : 9
% 0.21/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.49  # Initial clauses                      : 16
% 0.21/0.49  # Removed in clause preprocessing      : 2
% 0.21/0.49  # Initial clauses in saturation        : 14
% 0.21/0.49  # Processed clauses                    : 1635
% 0.21/0.49  # ...of these trivial                  : 14
% 0.21/0.49  # ...subsumed                          : 1278
% 0.21/0.49  # ...remaining for further processing  : 343
% 0.21/0.49  # Other redundant clauses eliminated   : 6
% 0.21/0.49  # Clauses deleted for lack of memory   : 0
% 0.21/0.49  # Backward-subsumed                    : 9
% 0.21/0.49  # Backward-rewritten                   : 6
% 0.21/0.49  # Generated clauses                    : 4725
% 0.21/0.49  # ...of the previous two non-trivial   : 3480
% 0.21/0.49  # Contextual simplify-reflections      : 21
% 0.21/0.49  # Paramodulations                      : 4709
% 0.21/0.49  # Factorizations                       : 10
% 0.21/0.49  # Equation resolutions                 : 6
% 0.21/0.49  # Propositional unsat checks           : 0
% 0.21/0.49  #    Propositional check models        : 0
% 0.21/0.49  #    Propositional check unsatisfiable : 0
% 0.21/0.49  #    Propositional clauses             : 0
% 0.21/0.49  #    Propositional clauses after purity: 0
% 0.21/0.49  #    Propositional unsat core size     : 0
% 0.21/0.49  #    Propositional preprocessing time  : 0.000
% 0.21/0.49  #    Propositional encoding time       : 0.000
% 0.21/0.49  #    Propositional solver time         : 0.000
% 0.21/0.49  #    Success case prop preproc time    : 0.000
% 0.21/0.49  #    Success case prop encoding time   : 0.000
% 0.21/0.49  #    Success case prop solver time     : 0.000
% 0.21/0.49  # Current number of processed clauses  : 312
% 0.21/0.49  #    Positive orientable unit clauses  : 15
% 0.21/0.49  #    Positive unorientable unit clauses: 0
% 0.21/0.49  #    Negative unit clauses             : 4
% 0.21/0.49  #    Non-unit-clauses                  : 293
% 0.21/0.49  # Current number of unprocessed clauses: 1840
% 0.21/0.49  # ...number of literals in the above   : 8764
% 0.21/0.49  # Current number of archived formulas  : 0
% 0.21/0.49  # Current number of archived clauses   : 31
% 0.21/0.49  # Clause-clause subsumption calls (NU) : 20939
% 0.21/0.49  # Rec. Clause-clause subsumption calls : 7469
% 0.21/0.49  # Non-unit clause-clause subsumptions  : 1298
% 0.21/0.49  # Unit Clause-clause subsumption calls : 128
% 0.21/0.49  # Rewrite failures with RHS unbound    : 0
% 0.21/0.49  # BW rewrite match attempts            : 7
% 0.21/0.49  # BW rewrite match successes           : 5
% 0.21/0.49  # Condensation attempts                : 0
% 0.21/0.49  # Condensation successes               : 0
% 0.21/0.49  # Termbank termtop insertions          : 124567
% 0.21/0.49  
% 0.21/0.49  # -------------------------------------------------
% 0.21/0.49  # User time                : 0.146 s
% 0.21/0.49  # System time              : 0.004 s
% 0.21/0.49  # Total time               : 0.150 s
% 0.21/0.49  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
