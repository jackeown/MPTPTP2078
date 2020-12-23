%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0247+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:17 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 ( 277 expanded)
%              Number of clauses        :   22 ( 122 expanded)
%              Number of leaves         :    2 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 (1653 expanded)
%              Number of equality atoms :   60 (1158 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_zfmisc_1)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k2_tarski(X2,X3))
      <=> ~ ( X1 != k1_xboole_0
            & X1 != k1_tarski(X2)
            & X1 != k1_tarski(X3)
            & X1 != k2_tarski(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t42_zfmisc_1])).

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

fof(c_0_4,negated_conjecture,
    ( ( esk1_0 != k1_xboole_0
      | ~ r1_tarski(esk1_0,k2_tarski(esk2_0,esk3_0)) )
    & ( esk1_0 != k1_tarski(esk2_0)
      | ~ r1_tarski(esk1_0,k2_tarski(esk2_0,esk3_0)) )
    & ( esk1_0 != k1_tarski(esk3_0)
      | ~ r1_tarski(esk1_0,k2_tarski(esk2_0,esk3_0)) )
    & ( esk1_0 != k2_tarski(esk2_0,esk3_0)
      | ~ r1_tarski(esk1_0,k2_tarski(esk2_0,esk3_0)) )
    & ( r1_tarski(esk1_0,k2_tarski(esk2_0,esk3_0))
      | esk1_0 = k1_xboole_0
      | esk1_0 = k1_tarski(esk2_0)
      | esk1_0 = k1_tarski(esk3_0)
      | esk1_0 = k2_tarski(esk2_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])])).

cnf(c_0_5,plain,
    ( r1_tarski(X1,k2_tarski(X3,X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( r1_tarski(esk1_0,k2_tarski(esk2_0,esk3_0))
    | esk1_0 = k1_xboole_0
    | esk1_0 = k1_tarski(esk2_0)
    | esk1_0 = k1_tarski(esk3_0)
    | esk1_0 = k2_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) = esk1_0
    | k1_tarski(esk3_0) = esk1_0
    | k1_tarski(esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,negated_conjecture,
    ( esk1_0 != k1_tarski(esk3_0)
    | ~ r1_tarski(esk1_0,k2_tarski(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) = esk1_0
    | k1_tarski(esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0
    | r1_tarski(esk1_0,k2_tarski(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) = esk1_0
    | k1_tarski(esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_9])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_16,negated_conjecture,
    ( esk1_0 != k1_tarski(esk2_0)
    | ~ r1_tarski(esk1_0,k2_tarski(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) = esk1_0
    | esk1_0 = k1_xboole_0
    | r1_tarski(esk1_0,k2_tarski(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( esk1_0 != k2_tarski(esk2_0,esk3_0)
    | ~ r1_tarski(esk1_0,k2_tarski(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | r1_tarski(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_23,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | ~ r1_tarski(esk1_0,k2_tarski(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_19]),c_0_21])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24]),c_0_25])]),
    [proof]).

%------------------------------------------------------------------------------
