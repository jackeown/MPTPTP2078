%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t115_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:58 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 660 expanded)
%              Number of clauses        :   30 ( 327 expanded)
%              Number of leaves         :    6 ( 172 expanded)
%              Depth                    :   14
%              Number of atoms          :   92 (1657 expanded)
%              Number of equality atoms :   26 ( 513 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X1) = k2_zfmisc_1(X2,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t115_zfmisc_1.p',t115_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t115_zfmisc_1.p',l54_zfmisc_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t115_zfmisc_1.p',t2_tarski)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t115_zfmisc_1.p',t7_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t115_zfmisc_1.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t115_zfmisc_1.p',d2_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X1) = k2_zfmisc_1(X2,X2)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t115_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X9,X10,X11,X12] :
      ( ( r2_hidden(X9,X11)
        | ~ r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X11,X12)) )
      & ( r2_hidden(X10,X12)
        | ~ r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X11,X12)) )
      & ( ~ r2_hidden(X9,X11)
        | ~ r2_hidden(X10,X12)
        | r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X11,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_8,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk1_0) = k2_zfmisc_1(esk2_0,esk2_0)
    & esk1_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk1_0) = k2_zfmisc_1(esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X13,X14] :
      ( ( ~ r2_hidden(esk3_2(X13,X14),X13)
        | ~ r2_hidden(esk3_2(X13,X14),X14)
        | X13 = X14 )
      & ( r2_hidden(esk3_2(X13,X14),X13)
        | r2_hidden(esk3_2(X13,X14),X14)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_14,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | ~ v1_xboole_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_19,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_20,negated_conjecture,
    ( esk2_0 = X1
    | r2_hidden(esk3_2(esk2_0,X1),esk1_0)
    | r2_hidden(esk3_2(esk2_0,X1),X1)
    | ~ r2_hidden(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( X1 = X2
    | r2_hidden(esk3_2(X1,X2),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_23,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk2_0,esk2_0))
    | ~ r2_hidden(X2,esk1_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk3_2(esk2_0,esk1_0),esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_20]),c_0_21])).

cnf(c_0_27,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X2,esk1_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r2_hidden(esk3_2(X1,X2),X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | r2_hidden(esk3_2(esk2_0,esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k1_xboole_0 = esk1_0
    | r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ r2_hidden(esk3_2(esk2_0,esk1_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | k1_xboole_0 = esk1_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_30]),c_0_32])).

cnf(c_0_34,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k1_xboole_0 = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_33]),c_0_34])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_35]),c_0_21])).

cnf(c_0_37,plain,
    ( esk2_0 = X1
    | r2_hidden(esk3_2(esk2_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_35]),c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_2(esk2_0,esk1_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_21])).

cnf(c_0_39,plain,
    ( v1_xboole_0(esk2_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_38]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
