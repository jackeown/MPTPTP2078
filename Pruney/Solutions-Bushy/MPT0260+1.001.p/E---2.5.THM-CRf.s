%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0260+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:18 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   35 (  75 expanded)
%              Number of clauses        :   20 (  37 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 264 expanded)
%              Number of equality atoms :   36 (  86 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
          & r2_hidden(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t55_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X27,X28] :
      ( ~ r1_xboole_0(X27,X28)
      | r1_xboole_0(X28,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_9,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)
    & r2_hidden(esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( r2_hidden(X19,X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k3_xboole_0(X16,X17) )
      & ( r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k3_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X16)
        | ~ r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k3_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | ~ r2_hidden(esk2_3(X21,X22,X23),X21)
        | ~ r2_hidden(esk2_3(X21,X22,X23),X22)
        | X23 = k3_xboole_0(X21,X22) )
      & ( r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k3_xboole_0(X21,X22) )
      & ( r2_hidden(esk2_3(X21,X22,X23),X22)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k3_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_11,plain,(
    ! [X25,X26] :
      ( ( ~ r1_xboole_0(X25,X26)
        | k3_xboole_0(X25,X26) = k1_xboole_0 )
      & ( k3_xboole_0(X25,X26) != k1_xboole_0
        | r1_xboole_0(X25,X26) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r1_xboole_0(esk5_0,k2_tarski(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X7
        | X10 = X8
        | X9 != k2_tarski(X7,X8) )
      & ( X11 != X7
        | r2_hidden(X11,X9)
        | X9 != k2_tarski(X7,X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k2_tarski(X7,X8) )
      & ( esk1_3(X12,X13,X14) != X12
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_tarski(X12,X13) )
      & ( esk1_3(X12,X13,X14) != X13
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_tarski(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | esk1_3(X12,X13,X14) = X12
        | esk1_3(X12,X13,X14) = X13
        | X14 = k2_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X29] : k3_xboole_0(X29,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k3_xboole_0(esk5_0,k2_tarski(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,k2_tarski(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_28,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_33,c_0_32]),
    [proof]).

%------------------------------------------------------------------------------
