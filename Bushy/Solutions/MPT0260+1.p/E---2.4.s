%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t55_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:09 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of clauses        :   17 (  18 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :  100 ( 108 expanded)
%              Number of equality atoms :   39 (  39 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t55_zfmisc_1.p',t55_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t55_zfmisc_1.p',d4_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t55_zfmisc_1.p',d7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t55_zfmisc_1.p',commutativity_k3_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t55_zfmisc_1.p',d2_tarski)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t55_zfmisc_1.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t55_zfmisc_1.p',dt_o_0_0_xboole_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t55_zfmisc_1.p',t7_boole)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
          & r2_hidden(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t55_zfmisc_1])).

fof(c_0_9,plain,(
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
      & ( ~ r2_hidden(esk5_3(X28,X29,X30),X30)
        | ~ r2_hidden(esk5_3(X28,X29,X30),X28)
        | ~ r2_hidden(esk5_3(X28,X29,X30),X29)
        | X30 = k3_xboole_0(X28,X29) )
      & ( r2_hidden(esk5_3(X28,X29,X30),X28)
        | r2_hidden(esk5_3(X28,X29,X30),X30)
        | X30 = k3_xboole_0(X28,X29) )
      & ( r2_hidden(esk5_3(X28,X29,X30),X29)
        | r2_hidden(esk5_3(X28,X29,X30),X30)
        | X30 = k3_xboole_0(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_10,plain,(
    ! [X32,X33] :
      ( ( ~ r1_xboole_0(X32,X33)
        | k3_xboole_0(X32,X33) = k1_xboole_0 )
      & ( k3_xboole_0(X32,X33) != k1_xboole_0
        | r1_xboole_0(X32,X33) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_11,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)
    & r2_hidden(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_12,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X14
        | X17 = X15
        | X16 != k2_tarski(X14,X15) )
      & ( X18 != X14
        | r2_hidden(X18,X16)
        | X16 != k2_tarski(X14,X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k2_tarski(X14,X15) )
      & ( esk4_3(X19,X20,X21) != X19
        | ~ r2_hidden(esk4_3(X19,X20,X21),X21)
        | X21 = k2_tarski(X19,X20) )
      & ( esk4_3(X19,X20,X21) != X20
        | ~ r2_hidden(esk4_3(X19,X20,X21),X21)
        | X21 = k2_tarski(X19,X20) )
      & ( r2_hidden(esk4_3(X19,X20,X21),X21)
        | esk4_3(X19,X20,X21) = X19
        | esk4_3(X19,X20,X21) = X20
        | X21 = k2_tarski(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_18,plain,(
    ! [X38] :
      ( ~ v1_xboole_0(X38)
      | X38 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( k3_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_24,plain,(
    ! [X39,X40] :
      ( ~ r2_hidden(X39,X40)
      | ~ v1_xboole_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,k2_tarski(esk1_0,esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_31,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
