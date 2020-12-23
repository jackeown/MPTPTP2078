%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:27 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 403 expanded)
%              Number of clauses        :   39 ( 162 expanded)
%              Number of leaves         :   15 ( 105 expanded)
%              Depth                    :   14
%              Number of atoms          :  205 (1158 expanded)
%              Number of equality atoms :   45 ( 220 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

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

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t21_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_xboole_0(X1,X2)
           => r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,k1_ordinal1(X2))
            <=> r1_ordinal1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_ordinal1])).

fof(c_0_16,plain,(
    ! [X37] : k1_ordinal1(X37) = k2_xboole_0(X37,k1_tarski(X37)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_17,plain,(
    ! [X30] : k2_tarski(X30,X30) = k1_tarski(X30) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    & v3_ordinal1(esk5_0)
    & ( ~ r2_hidden(esk4_0,k1_ordinal1(esk5_0))
      | ~ r1_ordinal1(esk4_0,esk5_0) )
    & ( r2_hidden(esk4_0,k1_ordinal1(esk5_0))
      | r1_ordinal1(esk4_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_19,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X31,X32] : k1_enumset1(X31,X31,X32) = k2_tarski(X31,X32) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X33,X34,X35] : k2_enumset1(X33,X33,X34,X35) = k1_enumset1(X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X42,X43] :
      ( ( ~ r1_ordinal1(X42,X43)
        | r1_tarski(X42,X43)
        | ~ v3_ordinal1(X42)
        | ~ v3_ordinal1(X43) )
      & ( ~ r1_tarski(X42,X43)
        | r1_ordinal1(X42,X43)
        | ~ v3_ordinal1(X42)
        | ~ v3_ordinal1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_0,k1_ordinal1(esk5_0))
    | r1_ordinal1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | ~ r2_xboole_0(X15,X16) )
      & ( X15 != X16
        | ~ r2_xboole_0(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | X15 = X16
        | r2_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r1_ordinal1(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k2_xboole_0(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_33,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X8)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k2_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_34,plain,(
    ! [X46,X47] :
      ( ~ v1_ordinal1(X46)
      | ~ v3_ordinal1(X47)
      | ~ r2_xboole_0(X46,X47)
      | r2_hidden(X46,X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).

cnf(c_0_35,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k2_xboole_0(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_ordinal1(esk5_0))
    | ~ r1_ordinal1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_39,plain,(
    ! [X48,X49] :
      ( ~ v3_ordinal1(X48)
      | ~ v3_ordinal1(X49)
      | r1_ordinal1(X48,X49)
      | r2_hidden(X49,X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( esk4_0 = esk5_0
    | r2_xboole_0(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k2_xboole_0(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_37])).

fof(c_0_43,plain,(
    ! [X36] :
      ( ( v1_ordinal1(X36)
        | ~ v3_ordinal1(X36) )
      & ( v2_ordinal1(X36)
        | ~ v3_ordinal1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_ordinal1(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k2_xboole_0(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_45,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( esk4_0 = esk5_0
    | r2_hidden(esk4_0,k2_xboole_0(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))
    | ~ v1_ordinal1(esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_31])]),c_0_42])).

cnf(c_0_47,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_48,plain,(
    ! [X38,X39,X40] :
      ( ( ~ v1_ordinal1(X38)
        | ~ r2_hidden(X39,X38)
        | r1_tarski(X39,X38) )
      & ( r2_hidden(esk3_1(X40),X40)
        | v1_ordinal1(X40) )
      & ( ~ r1_tarski(esk3_1(X40),X40)
        | v1_ordinal1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | ~ r2_hidden(esk4_0,k2_xboole_0(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_31]),c_0_32])])).

cnf(c_0_50,negated_conjecture,
    ( esk4_0 = esk5_0
    | r2_hidden(esk4_0,k2_xboole_0(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_32])])).

cnf(c_0_51,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( esk4_0 = esk5_0
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_53,plain,(
    ! [X44,X45] :
      ( ( ~ r2_hidden(X44,k1_ordinal1(X45))
        | r2_hidden(X44,X45)
        | X44 = X45 )
      & ( ~ r2_hidden(X44,X45)
        | r2_hidden(X44,k1_ordinal1(X45)) )
      & ( X44 != X45
        | r2_hidden(X44,k1_ordinal1(X45)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

fof(c_0_54,plain,(
    ! [X50,X51] :
      ( ~ r2_hidden(X50,X51)
      | ~ r1_tarski(X51,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_55,negated_conjecture,
    ( esk4_0 = esk5_0
    | r1_tarski(esk5_0,esk4_0)
    | ~ v1_ordinal1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_56,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( esk4_0 = esk5_0
    | r1_tarski(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_47]),c_0_32])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_63,negated_conjecture,
    ( esk4_0 = esk5_0
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k2_enumset1(X2,X2,X2,X2)))
    | X1 != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_50]),c_0_63])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_66]),c_0_66]),c_0_67])]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 10:22:57 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.35  # No SInE strategy applied
% 0.19/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.19/0.38  # and selection function SelectCQArNTNpEqFirst.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.029 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t34_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.19/0.38  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.19/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.38  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.19/0.38  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.19/0.38  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.19/0.38  fof(t21_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_xboole_0(X1,X2)=>r2_hidden(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 0.19/0.38  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.19/0.38  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.19/0.38  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.19/0.38  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.19/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(c_0_15, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2))))), inference(assume_negation,[status(cth)],[t34_ordinal1])).
% 0.19/0.38  fof(c_0_16, plain, ![X37]:k1_ordinal1(X37)=k2_xboole_0(X37,k1_tarski(X37)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.19/0.38  fof(c_0_17, plain, ![X30]:k2_tarski(X30,X30)=k1_tarski(X30), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.38  fof(c_0_18, negated_conjecture, (v3_ordinal1(esk4_0)&(v3_ordinal1(esk5_0)&((~r2_hidden(esk4_0,k1_ordinal1(esk5_0))|~r1_ordinal1(esk4_0,esk5_0))&(r2_hidden(esk4_0,k1_ordinal1(esk5_0))|r1_ordinal1(esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.19/0.38  cnf(c_0_19, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  fof(c_0_21, plain, ![X31, X32]:k1_enumset1(X31,X31,X32)=k2_tarski(X31,X32), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.38  fof(c_0_22, plain, ![X33, X34, X35]:k2_enumset1(X33,X33,X34,X35)=k1_enumset1(X33,X34,X35), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.38  fof(c_0_23, plain, ![X42, X43]:((~r1_ordinal1(X42,X43)|r1_tarski(X42,X43)|(~v3_ordinal1(X42)|~v3_ordinal1(X43)))&(~r1_tarski(X42,X43)|r1_ordinal1(X42,X43)|(~v3_ordinal1(X42)|~v3_ordinal1(X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk4_0,k1_ordinal1(esk5_0))|r1_ordinal1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_25, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.38  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  fof(c_0_28, plain, ![X15, X16]:(((r1_tarski(X15,X16)|~r2_xboole_0(X15,X16))&(X15!=X16|~r2_xboole_0(X15,X16)))&(~r1_tarski(X15,X16)|X15=X16|r2_xboole_0(X15,X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.19/0.38  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (r1_ordinal1(esk4_0,esk5_0)|r2_hidden(esk4_0,k2_xboole_0(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  fof(c_0_33, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(r2_hidden(X9,X6)|r2_hidden(X9,X7))|X8!=k2_xboole_0(X6,X7))&((~r2_hidden(X10,X6)|r2_hidden(X10,X8)|X8!=k2_xboole_0(X6,X7))&(~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k2_xboole_0(X6,X7))))&(((~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_xboole_0(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k2_xboole_0(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.19/0.38  fof(c_0_34, plain, ![X46, X47]:(~v1_ordinal1(X46)|(~v3_ordinal1(X47)|(~r2_xboole_0(X46,X47)|r2_hidden(X46,X47)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).
% 0.19/0.38  cnf(c_0_35, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (r1_tarski(esk4_0,esk5_0)|r2_hidden(esk4_0,k2_xboole_0(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])])).
% 0.19/0.38  cnf(c_0_37, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (~r2_hidden(esk4_0,k1_ordinal1(esk5_0))|~r1_ordinal1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  fof(c_0_39, plain, ![X48, X49]:(~v3_ordinal1(X48)|(~v3_ordinal1(X49)|(r1_ordinal1(X48,X49)|r2_hidden(X49,X48)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.19/0.38  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (esk4_0=esk5_0|r2_xboole_0(esk4_0,esk5_0)|r2_hidden(esk4_0,k2_xboole_0(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.38  cnf(c_0_42, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_37])).
% 0.19/0.38  fof(c_0_43, plain, ![X36]:((v1_ordinal1(X36)|~v3_ordinal1(X36))&(v2_ordinal1(X36)|~v3_ordinal1(X36))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (~r1_ordinal1(esk4_0,esk5_0)|~r2_hidden(esk4_0,k2_xboole_0(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_25]), c_0_26]), c_0_27])).
% 0.19/0.38  cnf(c_0_45, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (esk4_0=esk5_0|r2_hidden(esk4_0,k2_xboole_0(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))|~v1_ordinal1(esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_31])]), c_0_42])).
% 0.19/0.38  cnf(c_0_47, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  fof(c_0_48, plain, ![X38, X39, X40]:((~v1_ordinal1(X38)|(~r2_hidden(X39,X38)|r1_tarski(X39,X38)))&((r2_hidden(esk3_1(X40),X40)|v1_ordinal1(X40))&(~r1_tarski(esk3_1(X40),X40)|v1_ordinal1(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|~r2_hidden(esk4_0,k2_xboole_0(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_31]), c_0_32])])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (esk4_0=esk5_0|r2_hidden(esk4_0,k2_xboole_0(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_32])])).
% 0.19/0.38  cnf(c_0_51, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (esk4_0=esk5_0|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.38  fof(c_0_53, plain, ![X44, X45]:((~r2_hidden(X44,k1_ordinal1(X45))|(r2_hidden(X44,X45)|X44=X45))&((~r2_hidden(X44,X45)|r2_hidden(X44,k1_ordinal1(X45)))&(X44!=X45|r2_hidden(X44,k1_ordinal1(X45))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.19/0.38  fof(c_0_54, plain, ![X50, X51]:(~r2_hidden(X50,X51)|~r1_tarski(X51,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (esk4_0=esk5_0|r1_tarski(esk5_0,esk4_0)|~v1_ordinal1(esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.38  fof(c_0_56, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  cnf(c_0_57, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.38  cnf(c_0_58, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (esk4_0=esk5_0|r1_tarski(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_47]), c_0_32])])).
% 0.19/0.38  cnf(c_0_60, plain, (r2_hidden(X1,k1_ordinal1(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.38  cnf(c_0_61, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.38  cnf(c_0_62, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_25]), c_0_26]), c_0_27])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (esk4_0=esk5_0|~r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.38  cnf(c_0_64, plain, (r2_hidden(X1,k2_xboole_0(X2,k2_enumset1(X2,X2,X2,X2)))|X1!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_25]), c_0_26]), c_0_27])).
% 0.19/0.38  cnf(c_0_65, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_61])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (esk4_0=esk5_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_50]), c_0_63])).
% 0.19/0.38  cnf(c_0_67, plain, (r2_hidden(X1,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))), inference(er,[status(thm)],[c_0_64])).
% 0.19/0.38  cnf(c_0_68, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_58, c_0_65])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_66]), c_0_66]), c_0_67])]), c_0_68]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 70
% 0.19/0.38  # Proof object clause steps            : 39
% 0.19/0.38  # Proof object formula steps           : 31
% 0.19/0.38  # Proof object conjectures             : 20
% 0.19/0.38  # Proof object clause conjectures      : 17
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 19
% 0.19/0.38  # Proof object initial formulas used   : 15
% 0.19/0.38  # Proof object generating inferences   : 11
% 0.19/0.38  # Proof object simplifying inferences  : 35
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 16
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 41
% 0.19/0.38  # Removed in clause preprocessing      : 4
% 0.19/0.38  # Initial clauses in saturation        : 37
% 0.19/0.38  # Processed clauses                    : 95
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 4
% 0.19/0.38  # ...remaining for further processing  : 91
% 0.19/0.38  # Other redundant clauses eliminated   : 14
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 4
% 0.19/0.38  # Backward-rewritten                   : 14
% 0.19/0.38  # Generated clauses                    : 62
% 0.19/0.38  # ...of the previous two non-trivial   : 58
% 0.19/0.38  # Contextual simplify-reflections      : 3
% 0.19/0.38  # Paramodulations                      : 51
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 14
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 27
% 0.19/0.38  #    Positive orientable unit clauses  : 7
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 2
% 0.19/0.38  #    Non-unit-clauses                  : 18
% 0.19/0.38  # Current number of unprocessed clauses: 35
% 0.19/0.38  # ...number of literals in the above   : 82
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 57
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 283
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 195
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 11
% 0.19/0.38  # Unit Clause-clause subsumption calls : 22
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 11
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 3101
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.034 s
% 0.19/0.38  # System time              : 0.002 s
% 0.19/0.38  # Total time               : 0.036 s
% 0.19/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
