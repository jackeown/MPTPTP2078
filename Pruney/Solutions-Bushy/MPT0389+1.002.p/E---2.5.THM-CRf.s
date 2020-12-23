%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0389+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:33 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   41 (  70 expanded)
%              Number of clauses        :   29 (  33 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 326 expanded)
%              Number of equality atoms :   50 ( 132 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ( X1 = k1_xboole_0
        | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => ( X1 = k1_xboole_0
          | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t7_setfam_1])).

fof(c_0_7,plain,(
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

fof(c_0_8,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( ~ r1_tarski(X18,X19)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(X20,X19) )
      & ( r2_hidden(esk4_2(X21,X22),X21)
        | r1_tarski(X21,X22) )
      & ( ~ r2_hidden(esk4_2(X21,X22),X22)
        | r1_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_9,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0)
    & esk5_0 != k1_xboole_0
    & ~ r1_tarski(k1_setfam_1(esk6_0),k1_setfam_1(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_19,plain,(
    ! [X25,X26] :
      ( ~ r2_hidden(X25,X26)
      | ~ v1_xboole_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk1_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X1),X2)
    | r2_hidden(esk4_2(k1_setfam_1(X1),X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k1_setfam_1(esk5_0),X1),esk6_0)
    | r2_hidden(X1,k1_setfam_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

fof(c_0_23,plain,(
    ! [X24] :
      ( ~ v1_xboole_0(X24)
      | X24 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk1_3(X1,k1_setfam_1(X1),X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(k1_setfam_1(esk6_0),X1)
    | r2_hidden(esk4_2(k1_setfam_1(esk6_0),X1),esk1_3(esk5_0,k1_setfam_1(esk5_0),X2))
    | r2_hidden(X2,k1_setfam_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_setfam_1(X2)
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk6_0),k1_setfam_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_15])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(k1_setfam_1(esk6_0),X1)
    | r2_hidden(esk4_2(k1_setfam_1(esk6_0),X1),k1_setfam_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_18])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_setfam_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_30])).

cnf(c_0_38,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])]),
    [proof]).

%------------------------------------------------------------------------------
