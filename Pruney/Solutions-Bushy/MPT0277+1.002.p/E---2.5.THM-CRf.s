%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0277+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:21 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 401 expanded)
%              Number of clauses        :   29 ( 184 expanded)
%              Number of leaves         :    3 (  93 expanded)
%              Depth                    :   11
%              Number of atoms          :  110 (1996 expanded)
%              Number of equality atoms :   89 (1639 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t75_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(c_0_3,plain,(
    ! [X4,X5,X6] :
      ( ( ~ r1_tarski(X4,k2_tarski(X5,X6))
        | X4 = k1_xboole_0
        | X4 = k1_tarski(X5)
        | X4 = k1_tarski(X6)
        | X4 = k2_tarski(X5,X6) )
      & ( X4 != k1_xboole_0
        | r1_tarski(X4,k2_tarski(X5,X6)) )
      & ( X4 != k1_tarski(X5)
        | r1_tarski(X4,k2_tarski(X5,X6)) )
      & ( X4 != k1_tarski(X6)
        | r1_tarski(X4,k2_tarski(X5,X6)) )
      & ( X4 != k2_tarski(X5,X6)
        | r1_tarski(X4,k2_tarski(X5,X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_4,plain,(
    ! [X7,X8] :
      ( ( k4_xboole_0(X7,X8) != k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | k4_xboole_0(X7,X8) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
      <=> ~ ( X1 != k1_xboole_0
            & X1 != k1_tarski(X2)
            & X1 != k1_tarski(X3)
            & X1 != k2_tarski(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t75_zfmisc_1])).

cnf(c_0_6,plain,
    ( r1_tarski(X1,k2_tarski(X3,X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_9,negated_conjecture,
    ( ( esk1_0 != k1_xboole_0
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( esk1_0 != k1_tarski(esk2_0)
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( esk1_0 != k1_tarski(esk3_0)
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( esk1_0 != k2_tarski(esk2_0,esk3_0)
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) = k1_xboole_0
      | esk1_0 = k1_xboole_0
      | esk1_0 = k1_tarski(esk2_0)
      | esk1_0 = k1_tarski(esk3_0)
      | esk1_0 = k2_tarski(esk2_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( X1 = k2_tarski(X2,X3)
    | X1 = k1_tarski(X3)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | k4_xboole_0(X1,k2_tarski(X2,X3)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk1_0 = k1_tarski(esk2_0)
    | esk1_0 = k1_tarski(esk3_0)
    | esk1_0 = k2_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_15,plain,
    ( k4_xboole_0(k1_tarski(X1),k2_tarski(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) = esk1_0
    | k1_tarski(esk2_0) = esk1_0
    | k1_tarski(esk3_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk1_0 != k1_tarski(esk3_0)
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_tarski(X1,esk3_0)) = k1_xboole_0
    | k2_tarski(esk2_0,esk3_0) = esk1_0
    | k1_tarski(esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) = esk1_0
    | k1_tarski(esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_16])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( esk1_0 != k1_tarski(esk2_0)
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_tarski(esk2_0,X1)) = k1_xboole_0
    | k2_tarski(esk2_0,esk3_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_29,negated_conjecture,
    ( esk1_0 != k2_tarski(esk2_0,esk3_0)
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk1_0) = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_27]),c_0_30])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k1_xboole_0,k2_tarski(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_33])]),
    [proof]).

%------------------------------------------------------------------------------
