%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t28_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:04 EDT 2019

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   31 (  48 expanded)
%              Number of clauses        :   18 (  21 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 126 expanded)
%              Number of equality atoms :   64 (  96 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t28_zfmisc_1.p',t28_zfmisc_1)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t28_zfmisc_1.p',l45_zfmisc_1)).

fof(t8_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k1_tarski(X1) = k2_tarski(X2,X3)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t28_zfmisc_1.p',t8_zfmisc_1)).

fof(t10_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( k2_tarski(X1,X2) = k2_tarski(X3,X4)
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t28_zfmisc_1.p',t10_zfmisc_1)).

fof(fc3_xboole_0,axiom,(
    ! [X1,X2] : ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t28_zfmisc_1.p',fc3_xboole_0)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t28_zfmisc_1.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t28_zfmisc_1.p',d2_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
          & X1 != X3
          & X1 != X4 ) ),
    inference(assume_negation,[status(cth)],[t28_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r1_tarski(X13,k2_tarski(X14,X15))
        | X13 = k1_xboole_0
        | X13 = k1_tarski(X14)
        | X13 = k1_tarski(X15)
        | X13 = k2_tarski(X14,X15) )
      & ( X13 != k1_xboole_0
        | r1_tarski(X13,k2_tarski(X14,X15)) )
      & ( X13 != k1_tarski(X14)
        | r1_tarski(X13,k2_tarski(X14,X15)) )
      & ( X13 != k1_tarski(X15)
        | r1_tarski(X13,k2_tarski(X14,X15)) )
      & ( X13 != k2_tarski(X14,X15)
        | r1_tarski(X13,k2_tarski(X14,X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_9,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0))
    & esk1_0 != esk3_0
    & esk1_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X25,X26,X27] :
      ( k1_tarski(X25) != k2_tarski(X26,X27)
      | X25 = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_zfmisc_1])])).

cnf(c_0_11,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( X1 = X2
    | k1_tarski(X1) != k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( k2_tarski(esk3_0,esk4_0) = k2_tarski(esk1_0,esk2_0)
    | k1_tarski(esk3_0) = k2_tarski(esk1_0,esk2_0)
    | k1_tarski(esk4_0) = k2_tarski(esk1_0,esk2_0)
    | k2_tarski(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( k2_tarski(esk3_0,esk4_0) = k2_tarski(esk1_0,esk2_0)
    | k1_tarski(esk3_0) = k2_tarski(esk1_0,esk2_0)
    | k2_tarski(esk1_0,esk2_0) = k1_xboole_0
    | esk4_0 = X1
    | k2_tarski(esk1_0,esk2_0) != k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_16,negated_conjecture,
    ( esk1_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( k2_tarski(esk3_0,esk4_0) = k2_tarski(esk1_0,esk2_0)
    | k1_tarski(esk3_0) = k2_tarski(esk1_0,esk2_0)
    | k2_tarski(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_15]),c_0_16])).

fof(c_0_18,plain,(
    ! [X16,X17,X18,X19] :
      ( k2_tarski(X16,X17) != k2_tarski(X18,X19)
      | X16 = X18
      | X16 = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_zfmisc_1])])).

cnf(c_0_19,negated_conjecture,
    ( k2_tarski(esk3_0,esk4_0) = k2_tarski(esk1_0,esk2_0)
    | k2_tarski(esk1_0,esk2_0) = k1_xboole_0
    | esk3_0 = X1
    | k2_tarski(esk1_0,esk2_0) != k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( esk1_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( X1 = X3
    | X1 = X4
    | k2_tarski(X1,X2) != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k2_tarski(esk3_0,esk4_0) = k2_tarski(esk1_0,esk2_0)
    | k2_tarski(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_20])).

fof(c_0_23,plain,(
    ! [X28,X29] : ~ v1_xboole_0(k2_tarski(X28,X29)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_xboole_0])])).

cnf(c_0_24,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = k1_xboole_0
    | X1 = esk3_0
    | X1 = esk4_0
    | k2_tarski(X1,X2) != k2_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_26,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k2_tarski(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_24]),c_0_20]),c_0_16])).

cnf(c_0_29,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
