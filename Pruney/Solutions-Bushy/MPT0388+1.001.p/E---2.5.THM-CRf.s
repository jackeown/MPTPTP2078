%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0388+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:32 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   22 (  42 expanded)
%              Number of clauses        :   15 (  17 expanded)
%              Number of leaves         :    3 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 205 expanded)
%              Number of equality atoms :   33 (  69 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_setfam_1,conjecture,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r1_tarski(X2,X3) )
       => ( X1 = k1_xboole_0
          | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t6_setfam_1])).

fof(c_0_4,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( ~ r1_tarski(X18,X19)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(X20,X19) )
      & ( r2_hidden(esk4_2(X21,X22),X21)
        | r1_tarski(X21,X22) )
      & ( ~ r2_hidden(esk4_2(X21,X22),X22)
        | r1_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X26] :
      ( ( ~ r2_hidden(X26,esk5_0)
        | r1_tarski(esk6_0,X26) )
      & esk5_0 != k1_xboole_0
      & ~ r1_tarski(esk6_0,k1_setfam_1(esk5_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( ~ r1_tarski(esk6_0,k1_setfam_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_10,plain,(
    ! [X5,X6,X7,X8,X9,X11,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X7,X6)
        | ~ r2_hidden(X8,X5)
        | r2_hidden(X7,X8)
        | X6 != k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( r2_hidden(esk1_3(X5,X6,X9),X5)
        | r2_hidden(X9,X6)
        | X6 != k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( ~ r2_hidden(X9,esk1_3(X5,X6,X9))
        | r2_hidden(X9,X6)
        | X6 != k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X5,X11),X5)
        | ~ r2_hidden(esk2_2(X5,X11),X11)
        | X11 = k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( ~ r2_hidden(esk2_2(X5,X11),esk3_2(X5,X11))
        | ~ r2_hidden(esk2_2(X5,X11),X11)
        | X11 = k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( r2_hidden(esk2_2(X5,X11),X11)
        | ~ r2_hidden(X14,X5)
        | r2_hidden(esk2_2(X5,X11),X14)
        | X11 = k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( X16 != k1_setfam_1(X15)
        | X16 = k1_xboole_0
        | X15 != k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | X17 = k1_setfam_1(X15)
        | X15 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X2,esk5_0) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk4_2(esk6_0,k1_setfam_1(esk5_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk1_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk4_2(esk6_0,k1_setfam_1(esk5_0)),X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk1_3(X1,k1_setfam_1(X1),X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk4_2(esk6_0,k1_setfam_1(esk5_0)),esk1_3(esk5_0,X1,X2))
    | r2_hidden(X2,X1)
    | X1 != k1_setfam_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(esk4_2(esk6_0,k1_setfam_1(esk5_0)),k1_setfam_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_16]),c_0_20]),
    [proof]).

%------------------------------------------------------------------------------
