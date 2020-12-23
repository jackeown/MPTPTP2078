%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0078+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:00 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 (1523 expanded)
%              Number of clauses        :   63 ( 792 expanded)
%              Number of leaves         :    6 ( 339 expanded)
%              Depth                    :   23
%              Number of atoms          :  222 (8216 expanded)
%              Number of equality atoms :   56 (2466 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t71_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
        & r1_xboole_0(X1,X2)
        & r1_xboole_0(X3,X2) )
     => X1 = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_6,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X20)
        | r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k2_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X3,X2) )
       => X1 = X3 ) ),
    inference(assume_negation,[status(cth)],[t71_xboole_1])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk5_0) = k2_xboole_0(esk6_0,esk5_0)
    & r1_xboole_0(esk4_0,esk5_0)
    & r1_xboole_0(esk6_0,esk5_0)
    & esk4_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
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
      & ( ~ r2_hidden(esk3_3(X27,X28,X29),X29)
        | ~ r2_hidden(esk3_3(X27,X28,X29),X27)
        | ~ r2_hidden(esk3_3(X27,X28,X29),X28)
        | X29 = k3_xboole_0(X27,X28) )
      & ( r2_hidden(esk3_3(X27,X28,X29),X27)
        | r2_hidden(esk3_3(X27,X28,X29),X29)
        | X29 = k3_xboole_0(X27,X28) )
      & ( r2_hidden(esk3_3(X27,X28,X29),X28)
        | r2_hidden(esk3_3(X27,X28,X29),X29)
        | X29 = k3_xboole_0(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk5_0) = k2_xboole_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X31,X32] :
      ( ( ~ r1_xboole_0(X31,X32)
        | k3_xboole_0(X31,X32) = k1_xboole_0 )
      & ( k3_xboole_0(X31,X32) != k1_xboole_0
        | r1_xboole_0(X31,X32) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk6_0,esk5_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk3_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk3_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk3_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k3_xboole_0(X1,esk4_0) = esk4_0
    | r2_hidden(esk3_3(X1,esk4_0,esk4_0),esk6_0)
    | r2_hidden(esk3_3(X1,esk4_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk4_0) = esk4_0
    | r2_hidden(esk3_3(esk6_0,esk4_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( k3_xboole_0(esk6_0,X1) = X1
    | ~ r2_hidden(esk3_3(esk6_0,X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_32])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_37,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk4_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_24]),c_0_35])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_37])).

cnf(c_0_40,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X3) = X3
    | ~ r2_hidden(esk3_3(k2_xboole_0(X1,X2),X3,X3),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(X1,esk4_0) = esk4_0
    | r2_hidden(esk3_3(X1,esk4_0,esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_42,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_43,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(k2_xboole_0(X1,esk6_0),esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X1)
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_42])).

fof(c_0_46,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(X2,esk6_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_44])).

cnf(c_0_49,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,X1) = X1
    | r2_hidden(esk2_3(X1,X1,X1),X1) ),
    inference(ef,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(X2,esk6_0))
    | ~ r2_hidden(esk1_2(X1,k2_xboole_0(X2,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_50])).

cnf(c_0_55,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X2,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_13])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ r2_hidden(esk1_2(X1,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( esk4_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_12])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk4_0),esk6_0)
    | r1_tarski(esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_2(X1,esk4_0),esk5_0)
    | r1_tarski(X1,esk4_0)
    | ~ r2_hidden(esk1_2(X1,esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk4_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_61]),c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk4_0),esk5_0)
    | r1_tarski(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk4_0),esk5_0)
    | r2_hidden(esk1_2(esk4_0,esk6_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_64]),c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk4_0),esk5_0)
    | ~ r1_tarski(esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_64]),c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_29])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk4_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_65]),c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r2_hidden(esk1_2(X1,esk4_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,esk4_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_63])])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk6_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_72]),c_0_59])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_72]),c_0_59])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_73]),c_0_74]),
    [proof]).

%------------------------------------------------------------------------------
