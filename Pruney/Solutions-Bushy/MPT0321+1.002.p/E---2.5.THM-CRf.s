%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0321+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:25 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 532 expanded)
%              Number of clauses        :   35 ( 229 expanded)
%              Number of leaves         :    4 ( 128 expanded)
%              Depth                    :   13
%              Number of atoms          :  107 (1852 expanded)
%              Number of equality atoms :   44 ( 963 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8] :
      ( ( r2_hidden(X5,X7)
        | ~ r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)) )
      & ( r2_hidden(X6,X8)
        | ~ r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)) )
      & ( ~ r2_hidden(X5,X7)
        | ~ r2_hidden(X6,X8)
        | r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_6,plain,(
    ! [X14] :
      ( X14 = k1_xboole_0
      | r2_hidden(esk2_1(X14),X14) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_7,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0)
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & ( esk3_0 != esk5_0
      | esk4_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X9,X10] :
      ( ( ~ r2_hidden(esk1_2(X9,X10),X9)
        | ~ r2_hidden(esk1_2(X9,X10),X10)
        | X9 = X10 )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r2_hidden(esk1_2(X9,X10),X10)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk2_1(X1)),k2_zfmisc_1(X3,X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_hidden(k4_tarski(esk2_1(X1),esk2_1(X2)),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_12])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | X2 = X3
    | r2_hidden(k4_tarski(esk1_2(X2,X3),esk2_1(X1)),k2_zfmisc_1(X2,X1))
    | r2_hidden(esk1_2(X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( esk3_0 = X1
    | r2_hidden(esk1_2(esk3_0,X1),esk5_0)
    | r2_hidden(esk1_2(esk3_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_1(esk4_0)),k2_zfmisc_1(X2,esk6_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( esk5_0 = esk3_0
    | r2_hidden(esk1_2(esk3_0,esk5_0),esk5_0) ),
    inference(ef,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( X1 = X2
    | r2_hidden(k4_tarski(X3,esk1_2(X1,X2)),k2_zfmisc_1(X4,X1))
    | r2_hidden(esk1_2(X1,X2),X2)
    | ~ r2_hidden(X3,X4) ),
    inference(spm,[status(thm)],[c_0_8,c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( esk5_0 = esk3_0
    | r2_hidden(k4_tarski(esk1_2(esk3_0,esk5_0),esk2_1(esk4_0)),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( esk5_0 = esk3_0
    | ~ r2_hidden(esk1_2(esk3_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | X2 = X3
    | r2_hidden(k4_tarski(esk2_1(X1),esk1_2(X2,X3)),k2_zfmisc_1(X1,X2))
    | r2_hidden(esk1_2(X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( esk3_0 != esk5_0
    | esk4_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_28]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( esk4_0 = X1
    | r2_hidden(esk1_2(esk4_0,X1),esk6_0)
    | r2_hidden(esk1_2(esk4_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_30]),c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( esk6_0 != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_1(esk3_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_33]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(esk3_0),esk2_1(esk4_0)),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_35]),c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk1_2(esk4_0,esk6_0)),k2_zfmisc_1(X2,esk6_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk2_1(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk6_0) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_12,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(esk3_0),esk1_2(esk4_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk4_0,esk6_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_36]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_41]),c_0_42]),
    [proof]).

%------------------------------------------------------------------------------
