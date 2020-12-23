%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : ordinal1__t25_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:25 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   22 (  53 expanded)
%              Number of clauses        :   13 (  19 expanded)
%              Number of leaves         :    4 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 157 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => r3_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',t25_ordinal1)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',connectedness_r1_ordinal1)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',d9_xboole_0)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t25_ordinal1.p',redefinition_r1_ordinal1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => r3_xboole_0(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t25_ordinal1])).

fof(c_0_5,plain,(
    ! [X8,X9] :
      ( ~ v3_ordinal1(X8)
      | ~ v3_ordinal1(X9)
      | r1_ordinal1(X8,X9)
      | r1_ordinal1(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

fof(c_0_6,negated_conjecture,
    ( v3_ordinal1(esk1_0)
    & v3_ordinal1(esk2_0)
    & ~ r3_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X10,X11] :
      ( ( ~ r3_xboole_0(X10,X11)
        | r1_tarski(X10,X11)
        | r1_tarski(X11,X10) )
      & ( ~ r1_tarski(X10,X11)
        | r3_xboole_0(X10,X11) )
      & ( ~ r1_tarski(X11,X10)
        | r3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

fof(c_0_10,plain,(
    ! [X14,X15] :
      ( ( ~ r1_ordinal1(X14,X15)
        | r1_tarski(X14,X15)
        | ~ v3_ordinal1(X14)
        | ~ v3_ordinal1(X15) )
      & ( ~ r1_tarski(X14,X15)
        | r1_ordinal1(X14,X15)
        | ~ v3_ordinal1(X14)
        | ~ v3_ordinal1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_11,negated_conjecture,
    ( r1_ordinal1(X1,esk2_0)
    | r1_ordinal1(esk2_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v3_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( ~ r3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( r3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r1_ordinal1(esk2_0,esk1_0)
    | r1_ordinal1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r3_xboole_0(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( r1_ordinal1(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_8]),c_0_12])]),c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_19]),c_0_12]),c_0_8])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
