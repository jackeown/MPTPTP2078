%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t98_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:14 EDT 2019

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   35 (  76 expanded)
%              Number of clauses        :   24 (  36 expanded)
%              Number of leaves         :    5 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  112 ( 282 expanded)
%              Number of equality atoms :   22 (  60 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_xboole_0(X3,X2) )
     => r1_xboole_0(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t98_zfmisc_1.p',t98_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t98_zfmisc_1.p',d4_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t98_zfmisc_1.p',t4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t98_zfmisc_1.p',commutativity_k3_xboole_0)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t98_zfmisc_1.p',d4_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r1_xboole_0(X3,X2) )
       => r1_xboole_0(k3_tarski(X1),X2) ) ),
    inference(assume_negation,[status(cth)],[t98_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29,X30] :
      ( ( r2_hidden(X26,X23)
        | ~ r2_hidden(X26,X25)
        | X25 != k3_xboole_0(X23,X24) )
      & ( r2_hidden(X26,X24)
        | ~ r2_hidden(X26,X25)
        | X25 != k3_xboole_0(X23,X24) )
      & ( ~ r2_hidden(X27,X23)
        | ~ r2_hidden(X27,X24)
        | r2_hidden(X27,X25)
        | X25 != k3_xboole_0(X23,X24) )
      & ( ~ r2_hidden(esk6_3(X28,X29,X30),X30)
        | ~ r2_hidden(esk6_3(X28,X29,X30),X28)
        | ~ r2_hidden(esk6_3(X28,X29,X30),X29)
        | X30 = k3_xboole_0(X28,X29) )
      & ( r2_hidden(esk6_3(X28,X29,X30),X28)
        | r2_hidden(esk6_3(X28,X29,X30),X30)
        | X30 = k3_xboole_0(X28,X29) )
      & ( r2_hidden(esk6_3(X28,X29,X30),X29)
        | r2_hidden(esk6_3(X28,X29,X30),X30)
        | X30 = k3_xboole_0(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_7,negated_conjecture,(
    ! [X7] :
      ( ( ~ r2_hidden(X7,esk1_0)
        | r1_xboole_0(X7,esk2_0) )
      & ~ r1_xboole_0(k3_tarski(esk1_0),esk2_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X36,X37,X39,X40,X41] :
      ( ( r1_xboole_0(X36,X37)
        | r2_hidden(esk7_2(X36,X37),k3_xboole_0(X36,X37)) )
      & ( ~ r2_hidden(X41,k3_xboole_0(X39,X40))
        | ~ r1_xboole_0(X39,X40) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X10,X11] : k3_xboole_0(X10,X11) = k3_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_10,plain,(
    ! [X12,X13,X14,X16,X17,X18,X19,X21] :
      ( ( r2_hidden(X14,esk3_3(X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k3_tarski(X12) )
      & ( r2_hidden(esk3_3(X12,X13,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_tarski(X12) )
      & ( ~ r2_hidden(X16,X17)
        | ~ r2_hidden(X17,X12)
        | r2_hidden(X16,X13)
        | X13 != k3_tarski(X12) )
      & ( ~ r2_hidden(esk4_2(X18,X19),X19)
        | ~ r2_hidden(esk4_2(X18,X19),X21)
        | ~ r2_hidden(X21,X18)
        | X19 = k3_tarski(X18) )
      & ( r2_hidden(esk4_2(X18,X19),esk5_2(X18,X19))
        | r2_hidden(esk4_2(X18,X19),X19)
        | X19 = k3_tarski(X18) )
      & ( r2_hidden(esk5_2(X18,X19),X18)
        | r2_hidden(esk4_2(X18,X19),X19)
        | X19 = k3_tarski(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk7_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk7_2(k3_tarski(esk1_0),esk2_0),k3_xboole_0(esk2_0,k3_tarski(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( r2_hidden(esk3_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk7_2(k3_tarski(esk1_0),esk2_0),k3_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_3(esk1_0,k3_tarski(esk1_0),esk7_2(k3_tarski(esk1_0),esk2_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk7_2(k3_tarski(esk1_0),esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,esk3_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( r1_xboole_0(esk3_3(esk1_0,k3_tarski(esk1_0),esk7_2(k3_tarski(esk1_0),esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk7_2(k3_tarski(esk1_0),esk2_0),k3_xboole_0(esk2_0,X1))
    | ~ r2_hidden(esk7_2(k3_tarski(esk1_0),esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk7_2(k3_tarski(esk1_0),esk2_0),esk3_3(esk1_0,k3_tarski(esk1_0),esk7_2(k3_tarski(esk1_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(esk2_0,esk3_3(esk1_0,k3_tarski(esk1_0),esk7_2(k3_tarski(esk1_0),esk2_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
