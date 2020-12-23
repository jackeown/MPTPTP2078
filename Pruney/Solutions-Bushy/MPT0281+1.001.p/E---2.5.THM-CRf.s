%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0281+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:21 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 363 expanded)
%              Number of clauses        :   55 ( 185 expanded)
%              Number of leaves         :    5 (  77 expanded)
%              Depth                    :   16
%              Number of atoms          :  188 (1452 expanded)
%              Number of equality atoms :   52 ( 468 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t82_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) = k1_zfmisc_1(k2_xboole_0(X1,X2))
     => r3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_zfmisc_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(c_0_5,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X9,X8)
        | r1_tarski(X9,X7)
        | X8 != k1_zfmisc_1(X7) )
      & ( ~ r1_tarski(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k1_zfmisc_1(X7) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | ~ r1_tarski(esk1_2(X11,X12),X11)
        | X12 = k1_zfmisc_1(X11) )
      & ( r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(esk1_2(X11,X12),X11)
        | X12 = k1_zfmisc_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) = k1_zfmisc_1(k2_xboole_0(X1,X2))
       => r3_xboole_0(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t82_zfmisc_1])).

cnf(c_0_7,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,negated_conjecture,
    ( k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) = k1_zfmisc_1(k2_xboole_0(esk3_0,esk4_0))
    & ~ r3_xboole_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X16 != k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | r2_hidden(X18,X16)
        | X16 != k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k2_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k2_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X21)
        | r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k2_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) = k1_zfmisc_1(k2_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk3_0,esk4_0))
    | ~ r2_hidden(X1,k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_19,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk3_0,esk4_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk3_0,esk4_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_18])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk3_0,esk4_0))
    | k1_zfmisc_1(esk3_0) != k1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk3_0,esk4_0))
    | k1_zfmisc_1(esk4_0) != k1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | k2_xboole_0(X3,X2) != k1_zfmisc_1(X4)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(X1,X2)
    | k1_zfmisc_1(X2) != k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0))
    | ~ r1_tarski(X1,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_11])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk3_0,esk4_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk3_0,esk4_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | k2_xboole_0(X2,X3) != k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0))
    | ~ r1_tarski(X1,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk3_0,esk4_0),X1)
    | k1_zfmisc_1(X1) != k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(X1,X2)
    | k1_zfmisc_1(X2) != k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X1)
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(X1,X2)
    | k1_zfmisc_1(X2) != k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk3_0,esk4_0),X1)
    | r2_hidden(k2_xboole_0(esk3_0,esk4_0),X2)
    | k2_xboole_0(X2,X1) != k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_11])])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | k1_zfmisc_1(X1) != k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_29])).

cnf(c_0_40,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X1) = X1
    | r2_hidden(esk2_3(X1,X1,X1),X1) ),
    inference(ef,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | k1_zfmisc_1(X1) != k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_29])).

fof(c_0_43,plain,(
    ! [X23,X24] :
      ( ( ~ r3_xboole_0(X23,X24)
        | r1_tarski(X23,X24)
        | r1_tarski(X24,X23) )
      & ( ~ r1_tarski(X23,X24)
        | r3_xboole_0(X23,X24) )
      & ( ~ r1_tarski(X24,X23)
        | r3_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))
    | r2_hidden(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk4_0)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | r2_hidden(esk3_0,X2)
    | k2_xboole_0(X2,X1) != k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_39]),c_0_11])])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | r2_hidden(esk4_0,X2)
    | k2_xboole_0(X2,X1) != k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_42]),c_0_11])])).

cnf(c_0_48,negated_conjecture,
    ( ~ r3_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_49,plain,
    ( r3_xboole_0(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk4_0))
    | r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | X1 != k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk3_0))
    | r2_hidden(esk4_0,k1_zfmisc_1(esk4_0)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk3_0)
    | r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_52]),c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = esk3_0
    | r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = esk3_0
    | k2_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_58]),c_0_59])])).

cnf(c_0_61,negated_conjecture,
    ( k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) != k1_zfmisc_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_42])).

cnf(c_0_62,plain,
    ( r3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_63,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_60]),c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_63]),c_0_64]),
    [proof]).

%------------------------------------------------------------------------------
