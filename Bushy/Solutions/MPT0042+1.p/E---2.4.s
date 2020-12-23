%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t35_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:25 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   18 (  24 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   40 (  58 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t35_xboole_1.p',t1_xboole_1)).

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t35_xboole_1.p',t34_xboole_1)).

fof(t35_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k4_xboole_0(X1,X4),k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t35_xboole_1.p',t35_xboole_1)).

fof(t33_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t35_xboole_1.p',t33_xboole_1)).

fof(c_0_4,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X10,X11)
      | r1_tarski(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_5,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | r1_tarski(k4_xboole_0(X17,X16),k4_xboole_0(X17,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X4) )
       => r1_tarski(k4_xboole_0(X1,X4),k4_xboole_0(X2,X3)) ) ),
    inference(assume_negation,[status(cth)],[t35_xboole_1])).

cnf(c_0_7,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | r1_tarski(k4_xboole_0(X12,X14),k4_xboole_0(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_xboole_1])])).

fof(c_0_10,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k4_xboole_0(esk1_0,esk4_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k4_xboole_0(X2,X4))
    | ~ r1_tarski(X3,X4) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk1_0,esk4_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4))
    | ~ r1_tarski(X4,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
