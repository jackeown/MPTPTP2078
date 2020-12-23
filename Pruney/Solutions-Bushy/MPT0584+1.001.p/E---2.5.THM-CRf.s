%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0584+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:51 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   22 (  50 expanded)
%              Number of clauses        :   13 (  20 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 ( 138 expanded)
%              Number of equality atoms :   21 (  63 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    5 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t188_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3,X4] :
              ( ( r1_tarski(X3,X4)
                & k7_relat_1(X1,X4) = k7_relat_1(X2,X4) )
             => k7_relat_1(X1,X3) = k7_relat_1(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t188_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3,X4] :
                ( ( r1_tarski(X3,X4)
                  & k7_relat_1(X1,X4) = k7_relat_1(X2,X4) )
               => k7_relat_1(X1,X3) = k7_relat_1(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t188_relat_1])).

fof(c_0_5,plain,(
    ! [X7,X8,X9] :
      ( ~ v1_relat_1(X9)
      | k7_relat_1(k7_relat_1(X9,X7),X8) = k7_relat_1(X9,k3_xboole_0(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

fof(c_0_6,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_7,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k3_xboole_0(X10,X11) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & r1_tarski(esk3_0,esk4_0)
    & k7_relat_1(esk1_0,esk4_0) = k7_relat_1(esk2_0,esk4_0)
    & k7_relat_1(esk1_0,esk3_0) != k7_relat_1(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_9,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k7_relat_1(X1,k3_xboole_0(X2,X3)) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk4_0),esk3_0) = k7_relat_1(X1,esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_16,negated_conjecture,
    ( k7_relat_1(esk1_0,esk4_0) = k7_relat_1(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk2_0,esk4_0),esk3_0) = k7_relat_1(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( k7_relat_1(esk1_0,esk3_0) != k7_relat_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_18]),c_0_19])]),c_0_20]),
    [proof]).

%------------------------------------------------------------------------------
