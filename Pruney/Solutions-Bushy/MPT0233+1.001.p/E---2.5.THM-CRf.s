%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0233+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:16 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 227 expanded)
%              Number of clauses        :   25 ( 104 expanded)
%              Number of leaves         :    7 (  56 expanded)
%              Depth                    :   17
%              Number of atoms          :  105 ( 627 expanded)
%              Number of equality atoms :   87 ( 493 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(t28_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(t8_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k1_tarski(X1) = k2_tarski(X2,X3)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(t10_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( k2_tarski(X1,X2) = k2_tarski(X3,X4)
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_zfmisc_1)).

fof(fc3_xboole_0,axiom,(
    ! [X1,X2] : ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(c_0_7,plain,(
    ! [X7,X8,X9] :
      ( ( ~ r1_tarski(X7,k2_tarski(X8,X9))
        | X7 = k1_xboole_0
        | X7 = k1_tarski(X8)
        | X7 = k1_tarski(X9)
        | X7 = k2_tarski(X8,X9) )
      & ( X7 != k1_xboole_0
        | r1_tarski(X7,k2_tarski(X8,X9)) )
      & ( X7 != k1_tarski(X8)
        | r1_tarski(X7,k2_tarski(X8,X9)) )
      & ( X7 != k1_tarski(X9)
        | r1_tarski(X7,k2_tarski(X8,X9)) )
      & ( X7 != k2_tarski(X8,X9)
        | r1_tarski(X7,k2_tarski(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
          & X1 != X3
          & X1 != X4 ) ),
    inference(assume_negation,[status(cth)],[t28_zfmisc_1])).

cnf(c_0_9,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

fof(c_0_11,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0))
    & esk1_0 != esk3_0
    & esk1_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_12,plain,(
    ! [X14,X15,X16] :
      ( k1_tarski(X14) != k2_tarski(X15,X16)
      | X14 = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_zfmisc_1])])).

cnf(c_0_13,plain,
    ( X1 = k2_tarski(X2,X3)
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = o_0_0_xboole_0
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( X1 = X2
    | k1_tarski(X1) != k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = k2_tarski(esk3_0,esk4_0)
    | k2_tarski(esk1_0,esk2_0) = k1_tarski(esk4_0)
    | k2_tarski(esk1_0,esk2_0) = k1_tarski(esk3_0)
    | k2_tarski(esk1_0,esk2_0) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_17,plain,(
    ! [X10,X11,X12,X13] :
      ( k2_tarski(X10,X11) != k2_tarski(X12,X13)
      | X10 = X12
      | X10 = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_zfmisc_1])])).

cnf(c_0_18,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = k2_tarski(esk3_0,esk4_0)
    | k2_tarski(esk1_0,esk2_0) = k1_tarski(esk3_0)
    | k2_tarski(esk1_0,esk2_0) = o_0_0_xboole_0
    | X1 = esk1_0
    | k1_tarski(X1) != k1_tarski(esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( esk1_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( X1 = X3
    | X1 = X4
    | k2_tarski(X1,X2) != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = k2_tarski(esk3_0,esk4_0)
    | k2_tarski(esk1_0,esk2_0) = k1_tarski(esk3_0)
    | k2_tarski(esk1_0,esk2_0) = o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = k1_tarski(esk3_0)
    | k2_tarski(esk1_0,esk2_0) = o_0_0_xboole_0
    | X1 = esk2_0
    | X1 = esk1_0
    | k2_tarski(X1,X2) != k2_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,negated_conjecture,
    ( esk1_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = k1_tarski(esk3_0)
    | k2_tarski(esk1_0,esk2_0) = o_0_0_xboole_0
    | esk3_0 = esk2_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_23])).

fof(c_0_25,plain,(
    ! [X5,X6] : ~ v1_xboole_0(k2_tarski(X5,X6)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_xboole_0])])).

cnf(c_0_26,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = o_0_0_xboole_0
    | esk3_0 = esk2_0
    | X1 = esk1_0
    | k1_tarski(X1) != k1_tarski(esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_24])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = o_0_0_xboole_0
    | esk3_0 = esk2_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_23])).

cnf(c_0_29,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_30,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_31,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = k2_tarski(esk2_0,esk4_0)
    | k2_tarski(esk1_0,esk2_0) = k1_tarski(esk2_0)
    | k2_tarski(esk1_0,esk2_0) = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_30]),c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = k1_tarski(esk2_0)
    | k2_tarski(esk1_0,esk2_0) = o_0_0_xboole_0
    | esk1_0 = X1
    | esk1_0 = X2
    | k2_tarski(esk2_0,esk4_0) != k2_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = k1_tarski(esk2_0)
    | k2_tarski(esk1_0,esk2_0) = o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_19]),c_0_33])).

cnf(c_0_35,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = o_0_0_xboole_0
    | X1 = esk1_0
    | k1_tarski(X1) != k1_tarski(esk2_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_34])).

cnf(c_0_36,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_36]),c_0_29])]),
    [proof]).

%------------------------------------------------------------------------------
