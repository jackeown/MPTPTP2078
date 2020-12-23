%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0611+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:54 EST 2020

% Result     : Theorem 0.07s
% Output     : CNFRefutation 0.07s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 139 expanded)
%              Number of clauses        :   24 (  64 expanded)
%              Number of leaves         :    4 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 516 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t215_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
           => r1_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
             => r1_xboole_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t215_relat_1])).

fof(c_0_5,plain,(
    ! [X26,X27,X29,X30,X31] :
      ( ( r2_hidden(esk7_2(X26,X27),X26)
        | r1_xboole_0(X26,X27) )
      & ( r2_hidden(esk7_2(X26,X27),X27)
        | r1_xboole_0(X26,X27) )
      & ( ~ r2_hidden(X31,X29)
        | ~ r2_hidden(X31,X30)
        | ~ r1_xboole_0(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v1_relat_1(esk9_0)
    & r1_xboole_0(k2_relat_1(esk8_0),k2_relat_1(esk9_0))
    & ~ r1_xboole_0(esk8_0,esk9_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(esk7_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( ~ r1_xboole_0(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_11,plain,(
    ! [X5,X6,X9,X11,X12] :
      ( ( ~ v1_relat_1(X5)
        | ~ r2_hidden(X6,X5)
        | X6 = k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)) )
      & ( r2_hidden(esk3_1(X9),X9)
        | v1_relat_1(X9) )
      & ( esk3_1(X9) != k4_tarski(X11,X12)
        | v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(esk7_2(X1,X2),X1)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk7_2(esk8_0,esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_14,plain,(
    ! [X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( ~ r2_hidden(X15,X14)
        | r2_hidden(k4_tarski(esk4_3(X13,X14,X15),X15),X13)
        | X14 != k2_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X18,X17),X13)
        | r2_hidden(X17,X14)
        | X14 != k2_relat_1(X13) )
      & ( ~ r2_hidden(esk5_2(X19,X20),X20)
        | ~ r2_hidden(k4_tarski(X22,esk5_2(X19,X20)),X19)
        | X20 = k2_relat_1(X19) )
      & ( r2_hidden(esk5_2(X19,X20),X20)
        | r2_hidden(k4_tarski(esk6_2(X19,X20),esk5_2(X19,X20)),X19)
        | X20 = k2_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_15,plain,
    ( X2 = k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk7_2(esk9_0,X1),esk9_0)
    | ~ r2_hidden(esk7_2(esk8_0,esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk7_2(esk8_0,esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_8])).

cnf(c_0_19,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( k4_tarski(esk1_2(esk9_0,X1),esk2_2(esk9_0,X1)) = X1
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk7_2(esk9_0,esk8_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_10])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k4_tarski(esk1_2(esk9_0,esk7_2(esk9_0,esk8_0)),esk2_2(esk9_0,esk7_2(esk9_0,esk8_0))) = esk7_2(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk7_2(X1,esk8_0),esk8_0)
    | ~ r2_hidden(esk7_2(esk8_0,esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk8_0),k2_relat_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk2_2(esk9_0,esk7_2(esk9_0,esk8_0)),k2_relat_1(X1))
    | ~ r2_hidden(esk7_2(esk9_0,esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk7_2(esk9_0,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk9_0))
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk2_2(esk9_0,esk7_2(esk9_0,esk8_0)),k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk2_2(esk9_0,esk7_2(esk9_0,esk8_0)),k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])]),
    [proof]).

%------------------------------------------------------------------------------
