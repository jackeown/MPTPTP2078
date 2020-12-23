%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0321+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:25 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 532 expanded)
%              Number of clauses        :   36 ( 236 expanded)
%              Number of leaves         :    5 ( 126 expanded)
%              Depth                    :   18
%              Number of atoms          :  129 (1892 expanded)
%              Number of equality atoms :   59 (1055 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8] :
      ( ( r2_hidden(X5,X7)
        | ~ r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)) )
      & ( r2_hidden(X6,X8)
        | ~ r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)) )
      & ( ~ r2_hidden(X5,X7)
        | ~ r2_hidden(X6,X8)
        | r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_7,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0)
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & ( esk3_0 != esk5_0
      | esk4_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r2_hidden(X2,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_12,plain,(
    ! [X14] :
      ( X14 = k1_xboole_0
      | r2_hidden(esk2_1(X14),X14) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X2,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X11,X12] :
      ( ( ~ r2_hidden(esk1_2(X11,X12),X11)
        | ~ r2_hidden(esk1_2(X11,X12),X12)
        | X11 = X12 )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r2_hidden(esk1_2(X11,X12),X12)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_16,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = X1
    | r2_hidden(esk1_2(esk5_0,X1),esk3_0)
    | r2_hidden(esk1_2(esk5_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_9])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( esk5_0 = esk3_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk5_0,esk3_0),esk3_0) ),
    inference(ef,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X2,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_24,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_25,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = esk3_0
    | ~ r2_hidden(esk1_2(esk5_0,esk3_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_14]),c_0_23])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( esk5_0 = esk3_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_21])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k1_xboole_0
    | esk5_0 = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_28]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X2,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X2,esk3_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( esk6_0 = X1
    | r2_hidden(esk1_2(esk6_0,X1),esk4_0)
    | r2_hidden(esk1_2(esk6_0,X1),X1)
    | ~ r2_hidden(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( esk3_0 != esk5_0
    | esk4_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_39,negated_conjecture,
    ( esk6_0 = X1
    | r2_hidden(esk1_2(esk6_0,X1),esk4_0)
    | r2_hidden(esk1_2(esk6_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_14]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( esk6_0 != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_35])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_9])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_39]),c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_8])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk6_0,esk4_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_42]),c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_14]),c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_42])]),
    [proof]).

%------------------------------------------------------------------------------
