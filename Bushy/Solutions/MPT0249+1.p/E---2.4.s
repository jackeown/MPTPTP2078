%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t44_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:07 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   18 (  47 expanded)
%              Number of clauses        :   13 (  20 expanded)
%              Number of leaves         :    2 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 239 expanded)
%              Number of equality atoms :   75 ( 238 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t44_zfmisc_1.p',t43_zfmisc_1)).

fof(t44_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & X2 != X3
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t44_zfmisc_1.p',t44_zfmisc_1)).

fof(c_0_2,plain,(
    ! [X13,X14,X15] :
      ( ( X14 = k1_tarski(X13)
        | X14 = k1_xboole_0
        | X14 = k1_tarski(X13)
        | k1_tarski(X13) != k2_xboole_0(X14,X15) )
      & ( X15 = k1_xboole_0
        | X14 = k1_xboole_0
        | X14 = k1_tarski(X13)
        | k1_tarski(X13) != k2_xboole_0(X14,X15) )
      & ( X14 = k1_tarski(X13)
        | X15 = k1_tarski(X13)
        | X14 = k1_tarski(X13)
        | k1_tarski(X13) != k2_xboole_0(X14,X15) )
      & ( X15 = k1_xboole_0
        | X15 = k1_tarski(X13)
        | X14 = k1_tarski(X13)
        | k1_tarski(X13) != k2_xboole_0(X14,X15) )
      & ( X14 = k1_tarski(X13)
        | X14 = k1_xboole_0
        | X15 = k1_tarski(X13)
        | k1_tarski(X13) != k2_xboole_0(X14,X15) )
      & ( X15 = k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_tarski(X13)
        | k1_tarski(X13) != k2_xboole_0(X14,X15) )
      & ( X14 = k1_tarski(X13)
        | X15 = k1_tarski(X13)
        | X15 = k1_tarski(X13)
        | k1_tarski(X13) != k2_xboole_0(X14,X15) )
      & ( X15 = k1_xboole_0
        | X15 = k1_tarski(X13)
        | X15 = k1_tarski(X13)
        | k1_tarski(X13) != k2_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_zfmisc_1])])])).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & X2 != X3
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_zfmisc_1])).

cnf(c_0_4,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X2)
    | k1_tarski(X2) != k2_xboole_0(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

fof(c_0_5,negated_conjecture,
    ( k1_tarski(esk1_0) = k2_xboole_0(esk2_0,esk3_0)
    & esk2_0 != esk3_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | k1_tarski(X2) != k2_xboole_0(X3,X1) ),
    inference(cn,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k1_tarski(esk1_0) = k2_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( k1_tarski(X1) = esk3_0
    | k1_tarski(X1) != k1_tarski(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])).

cnf(c_0_10,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | k1_tarski(X2) != k2_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_11,negated_conjecture,
    ( k1_tarski(esk1_0) = esk3_0 ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | k1_tarski(X2) != k2_xboole_0(X1,X3) ),
    inference(cn,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_7,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( k1_tarski(X1) = esk2_0
    | k1_tarski(X1) != esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_16,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_11]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
