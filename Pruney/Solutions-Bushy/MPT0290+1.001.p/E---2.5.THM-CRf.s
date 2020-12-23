%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0290+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:22 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   35 (  87 expanded)
%              Number of clauses        :   26 (  44 expanded)
%              Number of leaves         :    4 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  115 ( 367 expanded)
%              Number of equality atoms :   20 (  72 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t97_zfmisc_1,conjecture,(
    ! [X1,X2] : r1_tarski(k3_tarski(k3_xboole_0(X1,X2)),k3_xboole_0(k3_tarski(X1),k3_tarski(X2))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k3_tarski(k3_xboole_0(X1,X2)),k3_xboole_0(k3_tarski(X1),k3_tarski(X2))) ),
    inference(assume_negation,[status(cth)],[t97_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(X13,esk2_3(X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( r2_hidden(esk2_3(X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(X15,X16)
        | ~ r2_hidden(X16,X11)
        | r2_hidden(X15,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(esk3_2(X17,X18),X18)
        | ~ r2_hidden(esk3_2(X17,X18),X20)
        | ~ r2_hidden(X20,X17)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk3_2(X17,X18),esk4_2(X17,X18))
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk4_2(X17,X18),X17)
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k3_tarski(esk6_0),k3_tarski(esk7_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28,X29] :
      ( ( r2_hidden(X25,X22)
        | ~ r2_hidden(X25,X24)
        | X24 != k3_xboole_0(X22,X23) )
      & ( r2_hidden(X25,X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k3_xboole_0(X22,X23) )
      & ( ~ r2_hidden(X26,X22)
        | ~ r2_hidden(X26,X23)
        | r2_hidden(X26,X24)
        | X24 != k3_xboole_0(X22,X23) )
      & ( ~ r2_hidden(esk5_3(X27,X28,X29),X29)
        | ~ r2_hidden(esk5_3(X27,X28,X29),X27)
        | ~ r2_hidden(esk5_3(X27,X28,X29),X28)
        | X29 = k3_xboole_0(X27,X28) )
      & ( r2_hidden(esk5_3(X27,X28,X29),X27)
        | r2_hidden(esk5_3(X27,X28,X29),X29)
        | X29 = k3_xboole_0(X27,X28) )
      & ( r2_hidden(esk5_3(X27,X28,X29),X28)
        | r2_hidden(esk5_3(X27,X28,X29),X29)
        | X29 = k3_xboole_0(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k3_tarski(esk6_0),k3_tarski(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk1_2(k3_tarski(k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k3_tarski(esk6_0),k3_tarski(esk7_0))),k3_tarski(k3_xboole_0(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk2_3(k3_xboole_0(esk6_0,esk7_0),k3_tarski(k3_xboole_0(esk6_0,esk7_0)),esk1_2(k3_tarski(k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k3_tarski(esk6_0),k3_tarski(esk7_0)))),k3_xboole_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk2_3(k3_xboole_0(esk6_0,esk7_0),k3_tarski(k3_xboole_0(esk6_0,esk7_0)),esk1_2(k3_tarski(k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k3_tarski(esk6_0),k3_tarski(esk7_0)))),esk7_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk2_3(k3_xboole_0(esk6_0,esk7_0),k3_tarski(k3_xboole_0(esk6_0,esk7_0)),esk1_2(k3_tarski(k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k3_tarski(esk6_0),k3_tarski(esk7_0)))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(esk7_0))
    | ~ r2_hidden(X1,esk2_3(k3_xboole_0(esk6_0,esk7_0),k3_tarski(k3_xboole_0(esk6_0,esk7_0)),esk1_2(k3_tarski(k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k3_tarski(esk6_0),k3_tarski(esk7_0))))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(k3_tarski(k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k3_tarski(esk6_0),k3_tarski(esk7_0))),esk2_3(k3_xboole_0(esk6_0,esk7_0),k3_tarski(k3_xboole_0(esk6_0,esk7_0)),esk1_2(k3_tarski(k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k3_tarski(esk6_0),k3_tarski(esk7_0))))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(esk6_0))
    | ~ r2_hidden(X1,esk2_3(k3_xboole_0(esk6_0,esk7_0),k3_tarski(k3_xboole_0(esk6_0,esk7_0)),esk1_2(k3_tarski(k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k3_tarski(esk6_0),k3_tarski(esk7_0))))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_2(k3_tarski(k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k3_tarski(esk6_0),k3_tarski(esk7_0))),k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_2(k3_tarski(k3_xboole_0(esk6_0,esk7_0)),k3_xboole_0(k3_tarski(esk6_0),k3_tarski(esk7_0))),k3_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_10]),
    [proof]).

%------------------------------------------------------------------------------
