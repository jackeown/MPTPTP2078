%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0117+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:37 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   37 (  70 expanded)
%              Number of clauses        :   20 (  31 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 123 expanded)
%              Number of equality atoms :   10 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t110_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t97_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k4_xboole_0(X1,X2),X3)
        & r1_tarski(k4_xboole_0(X2,X1),X3) )
     => r1_tarski(k5_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X2) )
       => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t110_xboole_1])).

fof(c_0_9,plain,(
    ! [X229,X230] : r1_tarski(k4_xboole_0(X229,X230),X229) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_10,plain,(
    ! [X119,X120] : k4_xboole_0(X119,X120) = k5_xboole_0(X119,k3_xboole_0(X119,X120)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_11,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_12,plain,(
    ! [X204,X205] :
      ( ~ r1_tarski(X204,X205)
      | k3_xboole_0(X204,X205) = X204 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_13,plain,(
    ! [X177,X178,X179] :
      ( ~ r1_tarski(X177,X178)
      | ~ r1_tarski(X178,X179)
      | r1_tarski(X177,X179) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_14,negated_conjecture,
    ( r1_tarski(esk14_0,esk15_0)
    & r1_tarski(esk16_0,esk15_0)
    & ~ r1_tarski(k5_xboole_0(esk14_0,esk16_0),esk15_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_15,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X401,X402,X403] :
      ( ~ r1_tarski(k4_xboole_0(X401,X402),X403)
      | ~ r1_tarski(k4_xboole_0(X402,X401),X403)
      | r1_tarski(k5_xboole_0(X401,X402),X403) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_xboole_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk16_0,esk15_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k4_xboole_0(X2,X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(X1,esk15_0)
    | ~ r1_tarski(X1,esk16_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_27,plain,(
    ! [X168,X169] : r1_tarski(k3_xboole_0(X168,X169),X168) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk14_0,esk15_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X3)
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_16]),c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk16_0,X1),esk15_0)
    | ~ r1_tarski(X1,esk16_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(X1,esk15_0)
    | ~ r1_tarski(X1,esk14_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k5_xboole_0(X1,esk16_0),esk15_0)
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,esk16_0)),esk15_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk14_0,X1),esk15_0)
    | ~ r1_tarski(X1,esk14_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk14_0,esk16_0),esk15_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_31])]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
