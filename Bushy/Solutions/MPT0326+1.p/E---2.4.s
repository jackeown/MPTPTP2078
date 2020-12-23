%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t139_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:01 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   26 (  45 expanded)
%              Number of clauses        :   15 (  18 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 ( 134 expanded)
%              Number of equality atoms :   26 (  42 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t139_zfmisc_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2,X3,X4] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
            | r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)) )
         => r1_tarski(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t139_zfmisc_1.p',t139_zfmisc_1)).

fof(t138_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t139_zfmisc_1.p',t138_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t139_zfmisc_1.p',t113_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t139_zfmisc_1.p',t2_xboole_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t139_zfmisc_1.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t139_zfmisc_1.p',d2_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2,X3,X4] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
              | r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)) )
           => r1_tarski(X2,X4) ) ) ),
    inference(assume_negation,[status(cth)],[t139_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X13,X14,X15,X16] :
      ( ( r1_tarski(X13,X15)
        | k2_zfmisc_1(X13,X14) = k1_xboole_0
        | ~ r1_tarski(k2_zfmisc_1(X13,X14),k2_zfmisc_1(X15,X16)) )
      & ( r1_tarski(X14,X16)
        | k2_zfmisc_1(X13,X14) = k1_xboole_0
        | ~ r1_tarski(k2_zfmisc_1(X13,X14),k2_zfmisc_1(X15,X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_zfmisc_1])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
      | r1_tarski(k2_zfmisc_1(esk2_0,esk1_0),k2_zfmisc_1(esk4_0,esk3_0)) )
    & ~ r1_tarski(esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | k2_zfmisc_1(X1,X3) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
    | r1_tarski(k2_zfmisc_1(esk2_0,esk1_0),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X11,X12] :
      ( ( k2_zfmisc_1(X11,X12) != k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | k2_zfmisc_1(X3,X1) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk1_0) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk1_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_11])).

fof(c_0_17,plain,(
    ! [X17] : r1_tarski(k1_xboole_0,X17) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_18,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_15])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_21,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_18]),c_0_19])])).

cnf(c_0_24,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
