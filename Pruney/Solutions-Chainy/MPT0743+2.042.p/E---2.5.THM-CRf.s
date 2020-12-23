%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:21 EST 2020

% Result     : Theorem 5.27s
% Output     : CNFRefutation 5.27s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 512 expanded)
%              Number of clauses        :   44 ( 204 expanded)
%              Number of leaves         :   15 ( 145 expanded)
%              Depth                    :   12
%              Number of atoms          :  157 ( 923 expanded)
%              Number of equality atoms :   19 ( 314 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,X2)
            <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_ordinal1])).

fof(c_0_16,plain,(
    ! [X37] : k1_ordinal1(X37) = k2_xboole_0(X37,k1_tarski(X37)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_17,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,negated_conjecture,
    ( v3_ordinal1(esk2_0)
    & v3_ordinal1(esk3_0)
    & ( ~ r2_hidden(esk2_0,esk3_0)
      | ~ r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) )
    & ( r2_hidden(esk2_0,esk3_0)
      | r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_19,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X24,X25,X26,X27] : k3_enumset1(X24,X24,X25,X26,X27) = k2_enumset1(X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X28,X29,X30,X31,X32] : k4_enumset1(X28,X28,X29,X30,X31,X32) = k3_enumset1(X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_25,plain,(
    ! [X41] :
      ( ~ v3_ordinal1(X41)
      | v3_ordinal1(k1_ordinal1(X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

fof(c_0_26,plain,(
    ! [X38,X39] :
      ( ( ~ r1_ordinal1(X38,X39)
        | r1_tarski(X38,X39)
        | ~ v3_ordinal1(X38)
        | ~ v3_ordinal1(X39) )
      & ( ~ r1_tarski(X38,X39)
        | r1_ordinal1(X38,X39)
        | ~ v3_ordinal1(X38)
        | ~ v3_ordinal1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_34,plain,(
    ! [X40] : r2_hidden(X40,k1_ordinal1(X40)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

fof(c_0_35,plain,(
    ! [X33,X34] :
      ( ( ~ r1_tarski(k1_tarski(X33),X34)
        | r2_hidden(X33,X34) )
      & ( ~ r2_hidden(X33,X34)
        | r1_tarski(k1_tarski(X33),X34) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_ordinal1(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k4_enumset1(X1,X1,X1,X1,X1,X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_41,plain,(
    ! [X35,X36] :
      ( ~ v3_ordinal1(X35)
      | ~ v3_ordinal1(X36)
      | r1_ordinal1(X35,X36)
      | r1_ordinal1(X36,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

fof(c_0_42,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_tarski(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0)
    | ~ v3_ordinal1(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_46,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k4_enumset1(X1,X1,X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_50,plain,
    ( r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_20]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_tarski(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_53,negated_conjecture,
    ( r1_ordinal1(X1,esk3_0)
    | r1_ordinal1(esk3_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_38])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(X1,k4_enumset1(X1,X1,X1,X1,X1,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0)
    | r1_tarski(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_20]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_57,negated_conjecture,
    ( r1_ordinal1(esk3_0,esk2_0)
    | r1_ordinal1(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_40])).

fof(c_0_58,plain,(
    ! [X42,X43] :
      ( ~ r2_hidden(X42,X43)
      | ~ r1_tarski(X43,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_59,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X17,X16)
      | r1_tarski(k2_xboole_0(X15,X17),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r1_ordinal1(esk3_0,esk2_0)
    | r1_tarski(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_57]),c_0_38]),c_0_40])])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    | r1_tarski(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_61]),c_0_40]),c_0_38])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0)
    | ~ r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0)
    | ~ r1_ordinal1(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_71,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( ~ r1_ordinal1(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_60])])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_38]),c_0_46])]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:16:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 5.27/5.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 5.27/5.44  # and selection function SelectLComplex.
% 5.27/5.44  #
% 5.27/5.44  # Preprocessing time       : 0.028 s
% 5.27/5.44  # Presaturation interreduction done
% 5.27/5.44  
% 5.27/5.44  # Proof found!
% 5.27/5.44  # SZS status Theorem
% 5.27/5.44  # SZS output start CNFRefutation
% 5.27/5.44  fof(t33_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 5.27/5.44  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 5.27/5.44  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.27/5.44  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.27/5.44  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 5.27/5.44  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 5.27/5.44  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 5.27/5.44  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 5.27/5.44  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 5.27/5.44  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 5.27/5.44  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.27/5.44  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 5.27/5.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.27/5.44  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.27/5.44  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.27/5.44  fof(c_0_15, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2))))), inference(assume_negation,[status(cth)],[t33_ordinal1])).
% 5.27/5.44  fof(c_0_16, plain, ![X37]:k1_ordinal1(X37)=k2_xboole_0(X37,k1_tarski(X37)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 5.27/5.44  fof(c_0_17, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 5.27/5.44  fof(c_0_18, negated_conjecture, (v3_ordinal1(esk2_0)&(v3_ordinal1(esk3_0)&((~r2_hidden(esk2_0,esk3_0)|~r1_ordinal1(k1_ordinal1(esk2_0),esk3_0))&(r2_hidden(esk2_0,esk3_0)|r1_ordinal1(k1_ordinal1(esk2_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 5.27/5.44  cnf(c_0_19, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.27/5.44  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 5.27/5.44  fof(c_0_21, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 5.27/5.44  fof(c_0_22, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 5.27/5.44  fof(c_0_23, plain, ![X24, X25, X26, X27]:k3_enumset1(X24,X24,X25,X26,X27)=k2_enumset1(X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 5.27/5.44  fof(c_0_24, plain, ![X28, X29, X30, X31, X32]:k4_enumset1(X28,X28,X29,X30,X31,X32)=k3_enumset1(X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 5.27/5.44  fof(c_0_25, plain, ![X41]:(~v3_ordinal1(X41)|v3_ordinal1(k1_ordinal1(X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 5.27/5.44  fof(c_0_26, plain, ![X38, X39]:((~r1_ordinal1(X38,X39)|r1_tarski(X38,X39)|(~v3_ordinal1(X38)|~v3_ordinal1(X39)))&(~r1_tarski(X38,X39)|r1_ordinal1(X38,X39)|(~v3_ordinal1(X38)|~v3_ordinal1(X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 5.27/5.44  cnf(c_0_27, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_ordinal1(k1_ordinal1(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.27/5.44  cnf(c_0_28, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 5.27/5.44  cnf(c_0_29, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 5.27/5.44  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.27/5.44  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.27/5.44  cnf(c_0_32, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.27/5.44  cnf(c_0_33, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 5.27/5.44  fof(c_0_34, plain, ![X40]:r2_hidden(X40,k1_ordinal1(X40)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 5.27/5.44  fof(c_0_35, plain, ![X33, X34]:((~r1_tarski(k1_tarski(X33),X34)|r2_hidden(X33,X34))&(~r2_hidden(X33,X34)|r1_tarski(k1_tarski(X33),X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 5.27/5.44  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 5.27/5.44  cnf(c_0_37, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_ordinal1(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 5.27/5.44  cnf(c_0_38, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.27/5.44  cnf(c_0_39, plain, (v3_ordinal1(k2_xboole_0(X1,k4_enumset1(X1,X1,X1,X1,X1,X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 5.27/5.44  cnf(c_0_40, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.27/5.44  fof(c_0_41, plain, ![X35, X36]:(~v3_ordinal1(X35)|~v3_ordinal1(X36)|(r1_ordinal1(X35,X36)|r1_ordinal1(X36,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 5.27/5.44  fof(c_0_42, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 5.27/5.44  cnf(c_0_43, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 5.27/5.44  cnf(c_0_44, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 5.27/5.44  cnf(c_0_45, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_tarski(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0)|~v3_ordinal1(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 5.27/5.44  cnf(c_0_46, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 5.27/5.44  cnf(c_0_47, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 5.27/5.44  cnf(c_0_48, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 5.27/5.44  cnf(c_0_49, plain, (r2_hidden(X1,k2_xboole_0(X1,k4_enumset1(X1,X1,X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 5.27/5.44  cnf(c_0_50, plain, (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_20]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 5.27/5.44  cnf(c_0_51, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_tarski(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])])).
% 5.27/5.44  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 5.27/5.44  cnf(c_0_53, negated_conjecture, (r1_ordinal1(X1,esk3_0)|r1_ordinal1(esk3_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_38])).
% 5.27/5.44  cnf(c_0_54, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(X1,k4_enumset1(X1,X1,X1,X1,X1,X1)),X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 5.27/5.44  cnf(c_0_55, negated_conjecture, (r1_tarski(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0)|r1_tarski(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 5.27/5.44  cnf(c_0_56, plain, (r2_hidden(X1,X2)|~r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_20]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 5.27/5.44  cnf(c_0_57, negated_conjecture, (r1_ordinal1(esk3_0,esk2_0)|r1_ordinal1(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_53, c_0_40])).
% 5.27/5.44  fof(c_0_58, plain, ![X42, X43]:(~r2_hidden(X42,X43)|~r1_tarski(X43,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 5.27/5.44  fof(c_0_59, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_tarski(X17,X16)|r1_tarski(k2_xboole_0(X15,X17),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 5.27/5.44  cnf(c_0_60, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 5.27/5.44  cnf(c_0_61, negated_conjecture, (r1_ordinal1(esk3_0,esk2_0)|r1_tarski(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_57]), c_0_38]), c_0_40])])).
% 5.27/5.44  cnf(c_0_62, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 5.27/5.44  cnf(c_0_63, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 5.27/5.44  cnf(c_0_64, negated_conjecture, (r1_tarski(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_50, c_0_60])).
% 5.27/5.44  cnf(c_0_65, negated_conjecture, (r1_tarski(esk2_0,esk3_0)|r1_tarski(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_61]), c_0_40]), c_0_38])])).
% 5.27/5.44  cnf(c_0_66, negated_conjecture, (~r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_62, c_0_60])).
% 5.27/5.44  cnf(c_0_67, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)|~r1_ordinal1(k1_ordinal1(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.27/5.44  cnf(c_0_68, negated_conjecture, (r1_tarski(k2_xboole_0(X1,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 5.27/5.44  cnf(c_0_69, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(sr,[status(thm)],[c_0_65, c_0_66])).
% 5.27/5.44  cnf(c_0_70, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)|~r1_ordinal1(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 5.27/5.44  cnf(c_0_71, plain, (r1_ordinal1(X1,X2)|~r1_tarski(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 5.27/5.44  cnf(c_0_72, negated_conjecture, (r1_tarski(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 5.27/5.44  cnf(c_0_73, negated_conjecture, (~r1_ordinal1(k2_xboole_0(esk2_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_60])])).
% 5.27/5.44  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_38]), c_0_46])]), c_0_73]), ['proof']).
% 5.27/5.44  # SZS output end CNFRefutation
% 5.27/5.44  # Proof object total steps             : 75
% 5.27/5.44  # Proof object clause steps            : 44
% 5.27/5.44  # Proof object formula steps           : 31
% 5.27/5.44  # Proof object conjectures             : 25
% 5.27/5.44  # Proof object clause conjectures      : 22
% 5.27/5.44  # Proof object formula conjectures     : 3
% 5.27/5.44  # Proof object initial clauses used    : 20
% 5.27/5.44  # Proof object initial formulas used   : 15
% 5.27/5.44  # Proof object generating inferences   : 14
% 5.27/5.44  # Proof object simplifying inferences  : 49
% 5.27/5.44  # Training examples: 0 positive, 0 negative
% 5.27/5.44  # Parsed axioms                        : 16
% 5.27/5.44  # Removed by relevancy pruning/SinE    : 0
% 5.27/5.44  # Initial clauses                      : 23
% 5.27/5.44  # Removed in clause preprocessing      : 6
% 5.27/5.44  # Initial clauses in saturation        : 17
% 5.27/5.44  # Processed clauses                    : 4068
% 5.27/5.44  # ...of these trivial                  : 10
% 5.27/5.44  # ...subsumed                          : 464
% 5.27/5.44  # ...remaining for further processing  : 3594
% 5.27/5.44  # Other redundant clauses eliminated   : 0
% 5.27/5.44  # Clauses deleted for lack of memory   : 0
% 5.27/5.44  # Backward-subsumed                    : 14
% 5.27/5.44  # Backward-rewritten                   : 15
% 5.27/5.44  # Generated clauses                    : 906570
% 5.27/5.44  # ...of the previous two non-trivial   : 903927
% 5.27/5.44  # Contextual simplify-reflections      : 1
% 5.27/5.44  # Paramodulations                      : 906561
% 5.27/5.44  # Factorizations                       : 0
% 5.27/5.44  # Equation resolutions                 : 0
% 5.27/5.44  # Propositional unsat checks           : 0
% 5.27/5.44  #    Propositional check models        : 0
% 5.27/5.44  #    Propositional check unsatisfiable : 0
% 5.27/5.44  #    Propositional clauses             : 0
% 5.27/5.44  #    Propositional clauses after purity: 0
% 5.27/5.44  #    Propositional unsat core size     : 0
% 5.27/5.44  #    Propositional preprocessing time  : 0.000
% 5.27/5.44  #    Propositional encoding time       : 0.000
% 5.27/5.44  #    Propositional solver time         : 0.000
% 5.27/5.44  #    Success case prop preproc time    : 0.000
% 5.27/5.44  #    Success case prop encoding time   : 0.000
% 5.27/5.44  #    Success case prop solver time     : 0.000
% 5.27/5.44  # Current number of processed clauses  : 3539
% 5.27/5.44  #    Positive orientable unit clauses  : 1315
% 5.27/5.44  #    Positive unorientable unit clauses: 0
% 5.27/5.44  #    Negative unit clauses             : 11
% 5.27/5.44  #    Non-unit-clauses                  : 2213
% 5.27/5.44  # Current number of unprocessed clauses: 899823
% 5.27/5.44  # ...number of literals in the above   : 920099
% 5.27/5.44  # Current number of archived formulas  : 0
% 5.27/5.44  # Current number of archived clauses   : 61
% 5.27/5.44  # Clause-clause subsumption calls (NU) : 467488
% 5.27/5.44  # Rec. Clause-clause subsumption calls : 467138
% 5.27/5.44  # Non-unit clause-clause subsumptions  : 476
% 5.27/5.44  # Unit Clause-clause subsumption calls : 72933
% 5.27/5.44  # Rewrite failures with RHS unbound    : 0
% 5.27/5.44  # BW rewrite match attempts            : 199463
% 5.27/5.44  # BW rewrite match successes           : 15
% 5.27/5.44  # Condensation attempts                : 0
% 5.27/5.44  # Condensation successes               : 0
% 5.27/5.44  # Termbank termtop insertions          : 23412548
% 5.27/5.47  
% 5.27/5.47  # -------------------------------------------------
% 5.27/5.47  # User time                : 4.746 s
% 5.27/5.47  # System time              : 0.374 s
% 5.27/5.47  # Total time               : 5.121 s
% 5.27/5.47  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
