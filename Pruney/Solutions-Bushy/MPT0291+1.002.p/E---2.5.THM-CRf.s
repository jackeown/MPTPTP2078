%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0291+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:22 EST 2020

% Result     : Theorem 4.25s
% Output     : CNFRefutation 4.25s
% Verified   : 
% Statistics : Number of formulae       :   37 (  57 expanded)
%              Number of clauses        :   26 (  29 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :  126 ( 245 expanded)
%              Number of equality atoms :   22 (  43 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t98_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_xboole_0(X3,X2) )
     => r1_xboole_0(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_5,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( r2_hidden(X21,X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k3_xboole_0(X18,X19) )
      & ( r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k3_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X18)
        | ~ r2_hidden(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k3_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk4_3(X23,X24,X25),X25)
        | ~ r2_hidden(esk4_3(X23,X24,X25),X23)
        | ~ r2_hidden(esk4_3(X23,X24,X25),X24)
        | X25 = k3_xboole_0(X23,X24) )
      & ( r2_hidden(esk4_3(X23,X24,X25),X23)
        | r2_hidden(esk4_3(X23,X24,X25),X25)
        | X25 = k3_xboole_0(X23,X24) )
      & ( r2_hidden(esk4_3(X23,X24,X25),X24)
        | r2_hidden(esk4_3(X23,X24,X25),X25)
        | X25 = k3_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_6,plain,(
    ! [X27,X28,X30,X31,X32] :
      ( ( r1_xboole_0(X27,X28)
        | r2_hidden(esk5_2(X27,X28),k3_xboole_0(X27,X28)) )
      & ( ~ r2_hidden(X32,k3_xboole_0(X30,X31))
        | ~ r1_xboole_0(X30,X31) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r1_xboole_0(X3,X2) )
       => r1_xboole_0(k3_tarski(X1),X2) ) ),
    inference(assume_negation,[status(cth)],[t98_zfmisc_1])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,(
    ! [X35] :
      ( ( ~ r2_hidden(X35,esk6_0)
        | r1_xboole_0(X35,esk7_0) )
      & ~ r1_xboole_0(k3_tarski(esk6_0),esk7_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk5_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_17,plain,(
    ! [X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(X9,esk1_3(X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k3_tarski(X7) )
      & ( r2_hidden(esk1_3(X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_tarski(X7) )
      & ( ~ r2_hidden(X11,X12)
        | ~ r2_hidden(X12,X7)
        | r2_hidden(X11,X8)
        | X8 != k3_tarski(X7) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | ~ r2_hidden(esk2_2(X13,X14),X16)
        | ~ r2_hidden(X16,X13)
        | X14 = k3_tarski(X13) )
      & ( r2_hidden(esk2_2(X13,X14),esk3_2(X13,X14))
        | r2_hidden(esk2_2(X13,X14),X14)
        | X14 = k3_tarski(X13) )
      & ( r2_hidden(esk3_2(X13,X14),X13)
        | r2_hidden(esk2_2(X13,X14),X14)
        | X14 = k3_tarski(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk6_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk5_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_22,negated_conjecture,
    ( r1_xboole_0(esk7_0,X1)
    | ~ r2_hidden(esk5_2(esk7_0,X1),X2)
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,esk1_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(esk7_0,X1)
    | ~ r2_hidden(esk1_3(X2,k3_tarski(X2),esk5_2(esk7_0,X1)),esk6_0)
    | ~ r2_hidden(esk5_2(esk7_0,X1),k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(esk7_0,X1)
    | ~ r2_hidden(esk5_2(esk7_0,X1),k3_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk5_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_16])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(esk7_0,k3_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),
    [proof]).

%------------------------------------------------------------------------------
