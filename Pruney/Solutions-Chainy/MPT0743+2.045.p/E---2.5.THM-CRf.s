%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:21 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 599 expanded)
%              Number of clauses        :   67 ( 267 expanded)
%              Number of leaves         :    9 ( 150 expanded)
%              Depth                    :   28
%              Number of atoms          :  241 (1781 expanded)
%              Number of equality atoms :   21 ( 140 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,X2)
            <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_ordinal1])).

fof(c_0_10,negated_conjecture,
    ( v3_ordinal1(esk2_0)
    & v3_ordinal1(esk3_0)
    & ( ~ r2_hidden(esk2_0,esk3_0)
      | ~ r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) )
    & ( r2_hidden(esk2_0,esk3_0)
      | r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X12] : k1_ordinal1(X12) = k2_xboole_0(X12,k1_tarski(X12)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_12,plain,(
    ! [X13,X14] :
      ( ( ~ r1_ordinal1(X13,X14)
        | r1_tarski(X13,X14)
        | ~ v3_ordinal1(X13)
        | ~ v3_ordinal1(X14) )
      & ( ~ r1_tarski(X13,X14)
        | r1_ordinal1(X13,X14)
        | ~ v3_ordinal1(X13)
        | ~ v3_ordinal1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X18] :
      ( ~ v3_ordinal1(X18)
      | v3_ordinal1(k1_ordinal1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

fof(c_0_16,plain,(
    ! [X10,X11] :
      ( ~ v3_ordinal1(X10)
      | ~ v3_ordinal1(X11)
      | r1_ordinal1(X10,X11)
      | r1_ordinal1(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0)
    | ~ v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_24,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_26,plain,(
    ! [X15] : r2_hidden(X15,k1_ordinal1(X15)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_27,plain,
    ( r1_ordinal1(X1,X2)
    | r1_tarski(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0)
    | ~ r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_32,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | ~ r1_tarski(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | r1_tarski(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk2_0,k1_tarski(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0)
    | ~ r1_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_14])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | r1_tarski(X2,X3)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r1_ordinal1(esk3_0,k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | ~ v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_21]),c_0_19])])).

cnf(c_0_41,plain,
    ( ~ r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_0,X1)
    | r1_tarski(X1,esk3_0)
    | ~ v3_ordinal1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_19])])).

fof(c_0_43,plain,(
    ! [X16,X17] :
      ( ( ~ r2_hidden(X16,k1_ordinal1(X17))
        | r2_hidden(X16,X17)
        | X16 = X17 )
      & ( ~ r2_hidden(X16,X17)
        | r2_hidden(X16,k1_ordinal1(X17)) )
      & ( X16 != X17
        | r2_hidden(X16,k1_ordinal1(X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | ~ v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_40]),c_0_19])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_0,k2_xboole_0(esk3_0,k1_tarski(esk3_0)))
    | ~ v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | ~ v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_39])])).

cnf(c_0_48,negated_conjecture,
    ( ~ v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))
    | ~ r1_tarski(k2_xboole_0(esk3_0,k1_tarski(esk3_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_45])).

cnf(c_0_49,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_46,c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | ~ v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(esk3_0,k1_tarski(esk3_0)))
    | ~ v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_33]),c_0_25])])).

cnf(c_0_52,negated_conjecture,
    ( X1 = esk2_0
    | r2_hidden(X1,esk2_0)
    | ~ v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk3_0,k1_tarski(esk3_0)))
    | ~ v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( X1 = esk2_0
    | r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_24]),c_0_25])])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_56,negated_conjecture,
    ( X1 = esk3_0
    | r2_hidden(X1,esk3_0)
    | ~ v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( esk1_2(esk3_0,X1) = esk2_0
    | r2_hidden(esk1_2(esk3_0,X1),esk2_0)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( X1 = esk3_0
    | r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_24]),c_0_19])])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_60,plain,
    ( esk1_2(k2_xboole_0(X1,k1_tarski(X1)),X2) = X1
    | r2_hidden(esk1_2(k2_xboole_0(X1,k1_tarski(X1)),X2),X1)
    | r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( esk1_2(esk3_0,X1) = esk2_0
    | r2_hidden(esk1_2(esk3_0,X1),X2)
    | r1_tarski(esk3_0,X1)
    | r1_tarski(X2,esk2_0)
    | ~ v3_ordinal1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_57]),c_0_25])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk2_0,X1)
    | r2_hidden(X2,esk3_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_42])).

cnf(c_0_63,negated_conjecture,
    ( esk1_2(esk2_0,X1) = esk3_0
    | r2_hidden(esk1_2(esk2_0,X1),esk3_0)
    | r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_55])).

cnf(c_0_64,plain,
    ( esk1_2(k2_xboole_0(X1,k1_tarski(X1)),X1) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_41])).

cnf(c_0_65,negated_conjecture,
    ( esk1_2(esk3_0,X1) = esk2_0
    | r1_tarski(X1,esk2_0)
    | r1_tarski(esk3_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk1_2(X1,X2),esk3_0)
    | r2_hidden(esk2_0,X1)
    | r1_tarski(X1,X2)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( esk1_2(esk2_0,esk3_0) = esk3_0
    | r1_tarski(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_63])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_64]),c_0_41])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_65]),c_0_37])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_25])]),c_0_68]),c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(esk1_2(X1,X2),esk3_0)
    | ~ r2_hidden(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk1_2(esk2_0,X1),esk3_0)
    | r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_55])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,esk2_0)
    | ~ r2_hidden(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_75])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(esk1_2(X1,X2),esk2_0)
    | ~ r2_hidden(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_76])).

cnf(c_0_78,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_79,negated_conjecture,
    ( esk1_2(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),X1) = esk2_0
    | r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),X1)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_60])).

cnf(c_0_80,negated_conjecture,
    ( ~ v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | ~ r2_hidden(esk2_0,esk3_0)
    | ~ r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_78]),c_0_19])])).

cnf(c_0_81,negated_conjecture,
    ( esk1_2(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0) = esk2_0
    | r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_39]),c_0_19])])).

cnf(c_0_82,negated_conjecture,
    ( ~ v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | ~ r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_39])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_81]),c_0_39])])).

cnf(c_0_84,negated_conjecture,
    ( ~ v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83])])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_24]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:24:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.50  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.21/0.50  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.21/0.50  #
% 0.21/0.50  # Preprocessing time       : 0.028 s
% 0.21/0.50  # Presaturation interreduction done
% 0.21/0.50  
% 0.21/0.50  # Proof found!
% 0.21/0.50  # SZS status Theorem
% 0.21/0.50  # SZS output start CNFRefutation
% 0.21/0.50  fof(t33_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 0.21/0.50  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.21/0.50  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.21/0.50  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.21/0.50  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 0.21/0.50  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.50  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.21/0.50  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.21/0.50  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.21/0.50  fof(c_0_9, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2))))), inference(assume_negation,[status(cth)],[t33_ordinal1])).
% 0.21/0.50  fof(c_0_10, negated_conjecture, (v3_ordinal1(esk2_0)&(v3_ordinal1(esk3_0)&((~r2_hidden(esk2_0,esk3_0)|~r1_ordinal1(k1_ordinal1(esk2_0),esk3_0))&(r2_hidden(esk2_0,esk3_0)|r1_ordinal1(k1_ordinal1(esk2_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.21/0.50  fof(c_0_11, plain, ![X12]:k1_ordinal1(X12)=k2_xboole_0(X12,k1_tarski(X12)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.21/0.50  fof(c_0_12, plain, ![X13, X14]:((~r1_ordinal1(X13,X14)|r1_tarski(X13,X14)|(~v3_ordinal1(X13)|~v3_ordinal1(X14)))&(~r1_tarski(X13,X14)|r1_ordinal1(X13,X14)|(~v3_ordinal1(X13)|~v3_ordinal1(X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.21/0.50  cnf(c_0_13, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_ordinal1(k1_ordinal1(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.50  cnf(c_0_14, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.50  fof(c_0_15, plain, ![X18]:(~v3_ordinal1(X18)|v3_ordinal1(k1_ordinal1(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.21/0.50  fof(c_0_16, plain, ![X10, X11]:(~v3_ordinal1(X10)|~v3_ordinal1(X11)|(r1_ordinal1(X10,X11)|r1_ordinal1(X11,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 0.21/0.50  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.50  cnf(c_0_18, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.50  cnf(c_0_19, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.50  cnf(c_0_20, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.50  cnf(c_0_21, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.50  fof(c_0_22, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.50  cnf(c_0_23, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0)|~v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.21/0.50  cnf(c_0_24, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_20, c_0_14])).
% 0.21/0.50  cnf(c_0_25, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.50  fof(c_0_26, plain, ![X15]:r2_hidden(X15,k1_ordinal1(X15)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 0.21/0.50  cnf(c_0_27, plain, (r1_ordinal1(X1,X2)|r1_tarski(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_17, c_0_21])).
% 0.21/0.50  cnf(c_0_28, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.50  cnf(c_0_29, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.21/0.50  cnf(c_0_30, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.50  cnf(c_0_31, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)|~r1_ordinal1(k1_ordinal1(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.50  fof(c_0_32, plain, ![X19, X20]:(~r2_hidden(X19,X20)|~r1_tarski(X20,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.21/0.50  cnf(c_0_33, plain, (r1_tarski(X1,X2)|r1_tarski(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_17, c_0_27])).
% 0.21/0.50  cnf(c_0_34, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r2_hidden(X1,esk3_0)|~r2_hidden(X1,k2_xboole_0(esk2_0,k1_tarski(esk2_0)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.50  cnf(c_0_35, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_30, c_0_14])).
% 0.21/0.50  cnf(c_0_36, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)|~r1_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0)), inference(rw,[status(thm)],[c_0_31, c_0_14])).
% 0.21/0.50  cnf(c_0_37, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.50  cnf(c_0_38, plain, (r2_hidden(X1,X2)|r1_tarski(X2,X3)|~v3_ordinal1(X2)|~v3_ordinal1(X3)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_28, c_0_33])).
% 0.21/0.50  cnf(c_0_39, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.50  cnf(c_0_40, negated_conjecture, (r1_ordinal1(esk3_0,k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|~v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|~r2_hidden(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_21]), c_0_19])])).
% 0.21/0.50  cnf(c_0_41, plain, (~r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X1)), inference(spm,[status(thm)],[c_0_37, c_0_35])).
% 0.21/0.50  cnf(c_0_42, negated_conjecture, (r2_hidden(esk2_0,X1)|r1_tarski(X1,esk3_0)|~v3_ordinal1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_19])])).
% 0.21/0.50  fof(c_0_43, plain, ![X16, X17]:((~r2_hidden(X16,k1_ordinal1(X17))|(r2_hidden(X16,X17)|X16=X17))&((~r2_hidden(X16,X17)|r2_hidden(X16,k1_ordinal1(X17)))&(X16!=X17|r2_hidden(X16,k1_ordinal1(X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.21/0.50  cnf(c_0_44, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|~v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|~r2_hidden(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_40]), c_0_19])])).
% 0.21/0.50  cnf(c_0_45, negated_conjecture, (r2_hidden(esk2_0,k2_xboole_0(esk3_0,k1_tarski(esk3_0)))|~v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.50  cnf(c_0_46, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.50  cnf(c_0_47, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|~v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_39])])).
% 0.21/0.50  cnf(c_0_48, negated_conjecture, (~v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))|~r1_tarski(k2_xboole_0(esk3_0,k1_tarski(esk3_0)),esk2_0)), inference(spm,[status(thm)],[c_0_37, c_0_45])).
% 0.21/0.50  cnf(c_0_49, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_46, c_0_14])).
% 0.21/0.50  cnf(c_0_50, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|~v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_47])).
% 0.21/0.50  cnf(c_0_51, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(esk3_0,k1_tarski(esk3_0)))|~v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_33]), c_0_25])])).
% 0.21/0.50  cnf(c_0_52, negated_conjecture, (X1=esk2_0|r2_hidden(X1,esk2_0)|~v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.50  cnf(c_0_53, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk3_0,k1_tarski(esk3_0)))|~v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_51])).
% 0.21/0.50  cnf(c_0_54, negated_conjecture, (X1=esk2_0|r2_hidden(X1,esk2_0)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_24]), c_0_25])])).
% 0.21/0.50  cnf(c_0_55, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.50  cnf(c_0_56, negated_conjecture, (X1=esk3_0|r2_hidden(X1,esk3_0)|~v3_ordinal1(k2_xboole_0(esk3_0,k1_tarski(esk3_0)))|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_49, c_0_53])).
% 0.21/0.50  cnf(c_0_57, negated_conjecture, (esk1_2(esk3_0,X1)=esk2_0|r2_hidden(esk1_2(esk3_0,X1),esk2_0)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.50  cnf(c_0_58, negated_conjecture, (X1=esk3_0|r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_24]), c_0_19])])).
% 0.21/0.50  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.50  cnf(c_0_60, plain, (esk1_2(k2_xboole_0(X1,k1_tarski(X1)),X2)=X1|r2_hidden(esk1_2(k2_xboole_0(X1,k1_tarski(X1)),X2),X1)|r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X2)), inference(spm,[status(thm)],[c_0_49, c_0_55])).
% 0.21/0.50  cnf(c_0_61, negated_conjecture, (esk1_2(esk3_0,X1)=esk2_0|r2_hidden(esk1_2(esk3_0,X1),X2)|r1_tarski(esk3_0,X1)|r1_tarski(X2,esk2_0)|~v3_ordinal1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_57]), c_0_25])])).
% 0.21/0.50  cnf(c_0_62, negated_conjecture, (r2_hidden(esk2_0,X1)|r2_hidden(X2,esk3_0)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_28, c_0_42])).
% 0.21/0.50  cnf(c_0_63, negated_conjecture, (esk1_2(esk2_0,X1)=esk3_0|r2_hidden(esk1_2(esk2_0,X1),esk3_0)|r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_58, c_0_55])).
% 0.21/0.50  cnf(c_0_64, plain, (esk1_2(k2_xboole_0(X1,k1_tarski(X1)),X1)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_41])).
% 0.21/0.50  cnf(c_0_65, negated_conjecture, (esk1_2(esk3_0,X1)=esk2_0|r1_tarski(X1,esk2_0)|r1_tarski(esk3_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_59, c_0_61])).
% 0.21/0.50  cnf(c_0_66, negated_conjecture, (r2_hidden(esk1_2(X1,X2),esk3_0)|r2_hidden(esk2_0,X1)|r1_tarski(X1,X2)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_62, c_0_55])).
% 0.21/0.50  cnf(c_0_67, negated_conjecture, (esk1_2(esk2_0,esk3_0)=esk3_0|r1_tarski(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_59, c_0_63])).
% 0.21/0.50  cnf(c_0_68, plain, (~r2_hidden(X1,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_64]), c_0_41])).
% 0.21/0.50  cnf(c_0_69, negated_conjecture, (r1_tarski(esk3_0,X1)|~v3_ordinal1(X1)|~r2_hidden(esk2_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_65]), c_0_37])).
% 0.21/0.50  cnf(c_0_70, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_25])]), c_0_68]), c_0_68])).
% 0.21/0.50  cnf(c_0_71, negated_conjecture, (r2_hidden(X1,X2)|~v3_ordinal1(X2)|~r2_hidden(X1,esk3_0)|~r2_hidden(esk2_0,X2)), inference(spm,[status(thm)],[c_0_28, c_0_69])).
% 0.21/0.50  cnf(c_0_72, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_70])).
% 0.21/0.50  cnf(c_0_73, negated_conjecture, (r1_tarski(X1,X2)|~v3_ordinal1(X2)|~r2_hidden(esk1_2(X1,X2),esk3_0)|~r2_hidden(esk2_0,X2)), inference(spm,[status(thm)],[c_0_59, c_0_71])).
% 0.21/0.50  cnf(c_0_74, negated_conjecture, (r2_hidden(esk1_2(esk2_0,X1),esk3_0)|r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_72, c_0_55])).
% 0.21/0.50  cnf(c_0_75, negated_conjecture, (r1_tarski(esk2_0,X1)|~v3_ordinal1(X1)|~r2_hidden(esk2_0,X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.21/0.50  cnf(c_0_76, negated_conjecture, (r2_hidden(X1,X2)|~v3_ordinal1(X2)|~r2_hidden(X1,esk2_0)|~r2_hidden(esk2_0,X2)), inference(spm,[status(thm)],[c_0_28, c_0_75])).
% 0.21/0.50  cnf(c_0_77, negated_conjecture, (r1_tarski(X1,X2)|~v3_ordinal1(X2)|~r2_hidden(esk1_2(X1,X2),esk2_0)|~r2_hidden(esk2_0,X2)), inference(spm,[status(thm)],[c_0_59, c_0_76])).
% 0.21/0.50  cnf(c_0_78, plain, (r1_ordinal1(X1,X2)|~r1_tarski(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.50  cnf(c_0_79, negated_conjecture, (esk1_2(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),X1)=esk2_0|r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),X1)|~v3_ordinal1(X1)|~r2_hidden(esk2_0,X1)), inference(spm,[status(thm)],[c_0_77, c_0_60])).
% 0.21/0.50  cnf(c_0_80, negated_conjecture, (~v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|~r2_hidden(esk2_0,esk3_0)|~r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_78]), c_0_19])])).
% 0.21/0.50  cnf(c_0_81, negated_conjecture, (esk1_2(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0)=esk2_0|r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_39]), c_0_19])])).
% 0.21/0.50  cnf(c_0_82, negated_conjecture, (~v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|~r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_39])])).
% 0.21/0.50  cnf(c_0_83, negated_conjecture, (r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_81]), c_0_39])])).
% 0.21/0.50  cnf(c_0_84, negated_conjecture, (~v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83])])).
% 0.21/0.50  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_24]), c_0_25])]), ['proof']).
% 0.21/0.50  # SZS output end CNFRefutation
% 0.21/0.50  # Proof object total steps             : 86
% 0.21/0.50  # Proof object clause steps            : 67
% 0.21/0.50  # Proof object formula steps           : 19
% 0.21/0.50  # Proof object conjectures             : 49
% 0.21/0.50  # Proof object clause conjectures      : 46
% 0.21/0.50  # Proof object formula conjectures     : 3
% 0.21/0.50  # Proof object initial clauses used    : 15
% 0.21/0.50  # Proof object initial formulas used   : 9
% 0.21/0.50  # Proof object generating inferences   : 44
% 0.21/0.50  # Proof object simplifying inferences  : 44
% 0.21/0.50  # Training examples: 0 positive, 0 negative
% 0.21/0.50  # Parsed axioms                        : 9
% 0.21/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.50  # Initial clauses                      : 17
% 0.21/0.50  # Removed in clause preprocessing      : 1
% 0.21/0.50  # Initial clauses in saturation        : 16
% 0.21/0.50  # Processed clauses                    : 818
% 0.21/0.50  # ...of these trivial                  : 7
% 0.21/0.50  # ...subsumed                          : 422
% 0.21/0.50  # ...remaining for further processing  : 389
% 0.21/0.50  # Other redundant clauses eliminated   : 1
% 0.21/0.50  # Clauses deleted for lack of memory   : 0
% 0.21/0.50  # Backward-subsumed                    : 27
% 0.21/0.50  # Backward-rewritten                   : 13
% 0.21/0.50  # Generated clauses                    : 5317
% 0.21/0.50  # ...of the previous two non-trivial   : 3958
% 0.21/0.50  # Contextual simplify-reflections      : 3
% 0.21/0.50  # Paramodulations                      : 5290
% 0.21/0.50  # Factorizations                       : 25
% 0.21/0.50  # Equation resolutions                 : 1
% 0.21/0.50  # Propositional unsat checks           : 0
% 0.21/0.50  #    Propositional check models        : 0
% 0.21/0.50  #    Propositional check unsatisfiable : 0
% 0.21/0.50  #    Propositional clauses             : 0
% 0.21/0.50  #    Propositional clauses after purity: 0
% 0.21/0.50  #    Propositional unsat core size     : 0
% 0.21/0.50  #    Propositional preprocessing time  : 0.000
% 0.21/0.50  #    Propositional encoding time       : 0.000
% 0.21/0.50  #    Propositional solver time         : 0.000
% 0.21/0.50  #    Success case prop preproc time    : 0.000
% 0.21/0.50  #    Success case prop encoding time   : 0.000
% 0.21/0.50  #    Success case prop solver time     : 0.000
% 0.21/0.50  # Current number of processed clauses  : 332
% 0.21/0.50  #    Positive orientable unit clauses  : 16
% 0.21/0.50  #    Positive unorientable unit clauses: 0
% 0.21/0.50  #    Negative unit clauses             : 17
% 0.21/0.50  #    Non-unit-clauses                  : 299
% 0.21/0.50  # Current number of unprocessed clauses: 3133
% 0.21/0.50  # ...number of literals in the above   : 18455
% 0.21/0.50  # Current number of archived formulas  : 0
% 0.21/0.50  # Current number of archived clauses   : 57
% 0.21/0.50  # Clause-clause subsumption calls (NU) : 5794
% 0.21/0.50  # Rec. Clause-clause subsumption calls : 2615
% 0.21/0.50  # Non-unit clause-clause subsumptions  : 357
% 0.21/0.50  # Unit Clause-clause subsumption calls : 120
% 0.21/0.50  # Rewrite failures with RHS unbound    : 0
% 0.21/0.50  # BW rewrite match attempts            : 15
% 0.21/0.50  # BW rewrite match successes           : 6
% 0.21/0.50  # Condensation attempts                : 0
% 0.21/0.50  # Condensation successes               : 0
% 0.21/0.50  # Termbank termtop insertions          : 141622
% 0.21/0.50  
% 0.21/0.50  # -------------------------------------------------
% 0.21/0.50  # User time                : 0.142 s
% 0.21/0.50  # System time              : 0.006 s
% 0.21/0.50  # Total time               : 0.148 s
% 0.21/0.50  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
