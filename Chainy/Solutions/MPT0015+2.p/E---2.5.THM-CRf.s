%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0015+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:31 EST 2020

% Result     : Theorem 6.32s
% Output     : CNFRefutation 6.32s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 101 expanded)
%              Number of clauses        :   30 (  50 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 414 expanded)
%              Number of equality atoms :   28 ( 114 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d3_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X2) )
       => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t8_xboole_1])).

fof(c_0_9,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( ~ r1_tarski(X19,X20)
        | ~ r2_hidden(X21,X19)
        | r2_hidden(X21,X20) )
      & ( r2_hidden(esk2_2(X22,X23),X22)
        | r1_tarski(X22,X23) )
      & ( ~ r2_hidden(esk2_2(X22,X23),X23)
        | r1_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_10,negated_conjecture,
    ( r1_tarski(esk14_0,esk15_0)
    & r1_tarski(esk16_0,esk15_0)
    & ~ r1_tarski(k2_xboole_0(esk14_0,esk16_0),esk15_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(X28,X27)
        | r2_hidden(X28,X25)
        | r2_hidden(X28,X26)
        | X27 != k2_xboole_0(X25,X26) )
      & ( ~ r2_hidden(X29,X25)
        | r2_hidden(X29,X27)
        | X27 != k2_xboole_0(X25,X26) )
      & ( ~ r2_hidden(X29,X26)
        | r2_hidden(X29,X27)
        | X27 != k2_xboole_0(X25,X26) )
      & ( ~ r2_hidden(esk3_3(X30,X31,X32),X30)
        | ~ r2_hidden(esk3_3(X30,X31,X32),X32)
        | X32 = k2_xboole_0(X30,X31) )
      & ( ~ r2_hidden(esk3_3(X30,X31,X32),X31)
        | ~ r2_hidden(esk3_3(X30,X31,X32),X32)
        | X32 = k2_xboole_0(X30,X31) )
      & ( r2_hidden(esk3_3(X30,X31,X32),X32)
        | r2_hidden(esk3_3(X30,X31,X32),X30)
        | r2_hidden(esk3_3(X30,X31,X32),X31)
        | X32 = k2_xboole_0(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk16_0,esk15_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | r2_hidden(esk3_3(X1,X2,X3),X1)
    | r2_hidden(esk3_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X119,X120] : r1_tarski(X119,k2_xboole_0(X119,X120)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_16,plain,(
    ! [X108,X109,X110] : k2_xboole_0(k2_xboole_0(X108,X109),X110) = k2_xboole_0(X108,k2_xboole_0(X109,X110)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_17,plain,(
    ! [X115,X116] : k2_xboole_0(X115,k2_xboole_0(X115,X116)) = k2_xboole_0(X115,X116) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

fof(c_0_18,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,esk15_0)
    | ~ r2_hidden(X1,esk16_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk3_3(X1,X2,X1),X1)
    | r2_hidden(esk3_3(X1,X2,X1),X2) ),
    inference(ef,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k2_xboole_0(X1,esk16_0) = X1
    | r2_hidden(esk3_3(X1,esk16_0,X1),esk15_0)
    | r2_hidden(esk3_3(X1,esk16_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk14_0,esk15_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_28,plain,(
    ! [X103,X104,X105] :
      ( ~ r1_tarski(X103,X104)
      | ~ r1_tarski(X104,X105)
      | r1_tarski(X103,X105) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( k2_xboole_0(esk15_0,esk16_0) = esk15_0
    | r2_hidden(esk3_3(esk15_0,esk16_0,esk15_0),esk15_0) ),
    inference(ef,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk3_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,esk15_0)
    | ~ r2_hidden(X1,esk14_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k2_xboole_0(esk15_0,esk16_0) = esk15_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( k2_xboole_0(X1,esk14_0) = X1
    | r2_hidden(esk3_3(X1,esk14_0,X1),esk15_0)
    | r2_hidden(esk3_3(X1,esk14_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_20])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk16_0),k2_xboole_0(X1,esk15_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k2_xboole_0(esk15_0,esk14_0) = esk15_0
    | r2_hidden(esk3_3(esk15_0,esk14_0,esk15_0),esk15_0) ),
    inference(ef,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk16_0),k2_xboole_0(esk15_0,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( k2_xboole_0(esk15_0,esk14_0) = esk15_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_42]),c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk14_0,esk16_0),esk15_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
