%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:29 EST 2020

% Result     : Theorem 1.00s
% Output     : CNFRefutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 505 expanded)
%              Number of clauses        :   80 ( 257 expanded)
%              Number of leaves         :   11 ( 118 expanded)
%              Depth                    :   19
%              Number of atoms          :  274 (1522 expanded)
%              Number of equality atoms :   87 ( 444 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

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

fof(t12_zfmisc_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t25_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))
        & X1 != X2
        & X1 != X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t38_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(k2_xboole_0(X14,X15),X16)
      | r1_tarski(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_13,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | k2_xboole_0(X17,X18) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_14,negated_conjecture,
    ( ( ~ r1_tarski(k2_tarski(esk4_0,esk5_0),esk6_0)
      | ~ r2_hidden(esk4_0,esk6_0)
      | ~ r2_hidden(esk5_0,esk6_0) )
    & ( r2_hidden(esk4_0,esk6_0)
      | r1_tarski(k2_tarski(esk4_0,esk5_0),esk6_0) )
    & ( r2_hidden(esk5_0,esk6_0)
      | r1_tarski(k2_tarski(esk4_0,esk5_0),esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_15,plain,(
    ! [X40,X41] : k1_enumset1(X40,X40,X41) = k2_tarski(X40,X41) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ( ~ r2_hidden(X35,X34)
        | X35 = X33
        | X34 != k1_tarski(X33) )
      & ( X36 != X33
        | r2_hidden(X36,X34)
        | X34 != k1_tarski(X33) )
      & ( ~ r2_hidden(esk3_2(X37,X38),X38)
        | esk3_2(X37,X38) != X37
        | X38 = k1_tarski(X37) )
      & ( r2_hidden(esk3_2(X37,X38),X38)
        | esk3_2(X37,X38) = X37
        | X38 = k1_tarski(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_17,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_18,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | r1_tarski(k2_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X44,X45] : r1_tarski(k1_tarski(X44),k2_tarski(X44,X45)) ),
    inference(variable_rename,[status(thm)],[t12_zfmisc_1])).

fof(c_0_24,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X26,X25)
        | X26 = X22
        | X26 = X23
        | X26 = X24
        | X25 != k1_enumset1(X22,X23,X24) )
      & ( X27 != X22
        | r2_hidden(X27,X25)
        | X25 != k1_enumset1(X22,X23,X24) )
      & ( X27 != X23
        | r2_hidden(X27,X25)
        | X25 != k1_enumset1(X22,X23,X24) )
      & ( X27 != X24
        | r2_hidden(X27,X25)
        | X25 != k1_enumset1(X22,X23,X24) )
      & ( esk2_4(X28,X29,X30,X31) != X28
        | ~ r2_hidden(esk2_4(X28,X29,X30,X31),X31)
        | X31 = k1_enumset1(X28,X29,X30) )
      & ( esk2_4(X28,X29,X30,X31) != X29
        | ~ r2_hidden(esk2_4(X28,X29,X30,X31),X31)
        | X31 = k1_enumset1(X28,X29,X30) )
      & ( esk2_4(X28,X29,X30,X31) != X30
        | ~ r2_hidden(esk2_4(X28,X29,X30,X31),X31)
        | X31 = k1_enumset1(X28,X29,X30) )
      & ( r2_hidden(esk2_4(X28,X29,X30,X31),X31)
        | esk2_4(X28,X29,X30,X31) = X28
        | esk2_4(X28,X29,X30,X31) = X29
        | esk2_4(X28,X29,X30,X31) = X30
        | X31 = k1_enumset1(X28,X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_25,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | r1_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X42,X43] :
      ( ( ~ r1_tarski(k1_tarski(X42),X43)
        | r2_hidden(X42,X43) )
      & ( ~ r2_hidden(X42,X43)
        | r1_tarski(k1_tarski(X42),X43) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | r1_tarski(k2_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( esk1_2(X1,X2) = X3
    | r1_tarski(X1,X2)
    | X1 != k1_tarski(X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k2_tarski(esk4_0,esk5_0),esk6_0)
    | ~ r2_hidden(esk4_0,esk6_0)
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | r1_tarski(X1,esk6_0)
    | ~ r1_tarski(X1,k1_enumset1(esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_tarski(X1),k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_22])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | r1_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_22])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( esk1_2(k1_tarski(X1),X2) = X1
    | r1_tarski(k1_tarski(X1),X2) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk6_0)
    | ~ r2_hidden(esk5_0,esk6_0)
    | ~ r1_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k1_enumset1(esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( X1 = X2
    | X3 != k1_tarski(X2)
    | ~ r1_tarski(k1_tarski(X1),X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_39])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k1_tarski(X1))
    | r1_tarski(k1_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_43])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk6_0)
    | ~ r1_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_tarski(X1))
    | X3 != k1_tarski(X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_tarski(X1),k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_59,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_55])).

fof(c_0_60,plain,(
    ! [X46,X47,X48] :
      ( ~ r1_tarski(k1_tarski(X46),k2_tarski(X47,X48))
      | X46 = X47
      | X46 = X48 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_zfmisc_1])])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k1_tarski(esk5_0),k2_xboole_0(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_54])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_44])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(X1,k1_tarski(X1))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k1_tarski(esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_46])).

cnf(c_0_66,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r1_tarski(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k1_tarski(esk5_0),X1)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_20])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X4)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_62])).

cnf(c_0_69,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | X2 != k1_tarski(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk6_0,k1_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_35])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k1_tarski(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_65])).

cnf(c_0_74,plain,
    ( X1 = X3
    | X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k1_enumset1(X2,X2,X3)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_22])).

cnf(c_0_75,plain,
    ( r1_tarski(k1_tarski(esk1_2(X1,X2)),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_26])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_tarski(esk5_0))
    | ~ r1_tarski(esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_67])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | X2 != k1_tarski(X4)
    | ~ r2_hidden(X1,k1_tarski(X4)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_59])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_enumset1(X1,X3,X4) ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | ~ r2_hidden(esk1_2(X1,esk6_0),k1_tarski(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_81,plain,
    ( esk1_2(k1_enumset1(X1,X1,X2),X3) = X1
    | esk1_2(k1_enumset1(X1,X1,X2),X3) = X2
    | r1_tarski(k1_enumset1(X1,X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(X1,X2)
    | k1_tarski(esk5_0) != k1_tarski(X1)
    | ~ r1_tarski(esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_63])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | X2 != k1_tarski(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( esk1_2(k1_enumset1(X1,X1,X2),esk6_0) = X1
    | r1_tarski(k1_enumset1(X1,X1,X2),esk6_0)
    | ~ r2_hidden(X2,k1_tarski(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk6_0,X2))
    | k1_tarski(esk5_0) != k1_tarski(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_44])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_52])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X3 != k1_tarski(X1)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_20])).

cnf(c_0_89,plain,
    ( r1_tarski(k1_tarski(X1),k1_enumset1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k1_enumset1(X1,X1,X2),esk6_0)
    | ~ r2_hidden(X2,k1_tarski(esk4_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk5_0,k2_xboole_0(esk6_0,X1)) ),
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_87,c_0_20])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(X1,k1_enumset1(X2,X3,X4))
    | k1_tarski(X2) != k1_tarski(X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k1_enumset1(X1,X1,esk4_0),esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_78])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk5_0,X1)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_20])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(X1,X2)
    | k1_tarski(X3) != k1_tarski(esk1_2(X1,X2))
    | ~ r1_tarski(k1_enumset1(X3,X4,X5),X2) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k1_enumset1(esk5_0,esk5_0,esk4_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_35])])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | k1_tarski(esk1_2(X1,esk6_0)) != k1_tarski(esk5_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_99,plain,
    ( esk1_2(k1_enumset1(X1,X1,X2),X3) = X2
    | r1_tarski(k1_enumset1(X1,X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_72,c_0_81])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k1_enumset1(X1,X1,X2),esk6_0)
    | k1_tarski(X2) != k1_tarski(esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k1_enumset1(esk4_0,esk4_0,X1),esk6_0)
    | k1_tarski(X1) != k1_tarski(esk5_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_46])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_101]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:09:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.00/1.18  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 1.00/1.18  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.00/1.18  #
% 1.00/1.18  # Preprocessing time       : 0.028 s
% 1.00/1.18  # Presaturation interreduction done
% 1.00/1.18  
% 1.00/1.18  # Proof found!
% 1.00/1.18  # SZS status Theorem
% 1.00/1.18  # SZS output start CNFRefutation
% 1.00/1.18  fof(t38_zfmisc_1, conjecture, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.00/1.18  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.00/1.18  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.00/1.18  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.00/1.18  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.00/1.18  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.00/1.18  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.00/1.18  fof(t12_zfmisc_1, axiom, ![X1, X2]:r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.00/1.18  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.00/1.18  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.00/1.18  fof(t25_zfmisc_1, axiom, ![X1, X2, X3]:~(((r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))&X1!=X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.00/1.18  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3)))), inference(assume_negation,[status(cth)],[t38_zfmisc_1])).
% 1.00/1.18  fof(c_0_12, plain, ![X14, X15, X16]:(~r1_tarski(k2_xboole_0(X14,X15),X16)|r1_tarski(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 1.00/1.18  fof(c_0_13, plain, ![X17, X18]:(~r1_tarski(X17,X18)|k2_xboole_0(X17,X18)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.00/1.18  fof(c_0_14, negated_conjecture, ((~r1_tarski(k2_tarski(esk4_0,esk5_0),esk6_0)|(~r2_hidden(esk4_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)))&((r2_hidden(esk4_0,esk6_0)|r1_tarski(k2_tarski(esk4_0,esk5_0),esk6_0))&(r2_hidden(esk5_0,esk6_0)|r1_tarski(k2_tarski(esk4_0,esk5_0),esk6_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 1.00/1.18  fof(c_0_15, plain, ![X40, X41]:k1_enumset1(X40,X40,X41)=k2_tarski(X40,X41), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.00/1.18  fof(c_0_16, plain, ![X33, X34, X35, X36, X37, X38]:(((~r2_hidden(X35,X34)|X35=X33|X34!=k1_tarski(X33))&(X36!=X33|r2_hidden(X36,X34)|X34!=k1_tarski(X33)))&((~r2_hidden(esk3_2(X37,X38),X38)|esk3_2(X37,X38)!=X37|X38=k1_tarski(X37))&(r2_hidden(esk3_2(X37,X38),X38)|esk3_2(X37,X38)=X37|X38=k1_tarski(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 1.00/1.18  fof(c_0_17, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.00/1.18  fof(c_0_18, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.00/1.18  cnf(c_0_19, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.00/1.18  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.00/1.18  cnf(c_0_21, negated_conjecture, (r2_hidden(esk4_0,esk6_0)|r1_tarski(k2_tarski(esk4_0,esk5_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.00/1.18  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.00/1.18  fof(c_0_23, plain, ![X44, X45]:r1_tarski(k1_tarski(X44),k2_tarski(X44,X45)), inference(variable_rename,[status(thm)],[t12_zfmisc_1])).
% 1.00/1.18  fof(c_0_24, plain, ![X22, X23, X24, X25, X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X26,X25)|(X26=X22|X26=X23|X26=X24)|X25!=k1_enumset1(X22,X23,X24))&(((X27!=X22|r2_hidden(X27,X25)|X25!=k1_enumset1(X22,X23,X24))&(X27!=X23|r2_hidden(X27,X25)|X25!=k1_enumset1(X22,X23,X24)))&(X27!=X24|r2_hidden(X27,X25)|X25!=k1_enumset1(X22,X23,X24))))&((((esk2_4(X28,X29,X30,X31)!=X28|~r2_hidden(esk2_4(X28,X29,X30,X31),X31)|X31=k1_enumset1(X28,X29,X30))&(esk2_4(X28,X29,X30,X31)!=X29|~r2_hidden(esk2_4(X28,X29,X30,X31),X31)|X31=k1_enumset1(X28,X29,X30)))&(esk2_4(X28,X29,X30,X31)!=X30|~r2_hidden(esk2_4(X28,X29,X30,X31),X31)|X31=k1_enumset1(X28,X29,X30)))&(r2_hidden(esk2_4(X28,X29,X30,X31),X31)|(esk2_4(X28,X29,X30,X31)=X28|esk2_4(X28,X29,X30,X31)=X29|esk2_4(X28,X29,X30,X31)=X30)|X31=k1_enumset1(X28,X29,X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 1.00/1.18  cnf(c_0_25, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.00/1.18  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.00/1.18  cnf(c_0_27, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.00/1.18  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 1.00/1.18  cnf(c_0_29, negated_conjecture, (r2_hidden(esk4_0,esk6_0)|r1_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0),esk6_0)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 1.00/1.18  cnf(c_0_30, plain, (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.00/1.18  fof(c_0_31, plain, ![X42, X43]:((~r1_tarski(k1_tarski(X42),X43)|r2_hidden(X42,X43))&(~r2_hidden(X42,X43)|r1_tarski(k1_tarski(X42),X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 1.00/1.18  cnf(c_0_32, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|r1_tarski(k2_tarski(esk4_0,esk5_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.00/1.18  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.00/1.18  cnf(c_0_34, plain, (esk1_2(X1,X2)=X3|r1_tarski(X1,X2)|X1!=k1_tarski(X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.00/1.18  cnf(c_0_35, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_27])).
% 1.00/1.18  cnf(c_0_36, negated_conjecture, (~r1_tarski(k2_tarski(esk4_0,esk5_0),esk6_0)|~r2_hidden(esk4_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.00/1.18  cnf(c_0_37, negated_conjecture, (r2_hidden(esk4_0,esk6_0)|r1_tarski(X1,esk6_0)|~r1_tarski(X1,k1_enumset1(esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.00/1.18  cnf(c_0_38, plain, (r1_tarski(k1_tarski(X1),k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[c_0_30, c_0_22])).
% 1.00/1.18  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.00/1.18  cnf(c_0_40, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.00/1.18  cnf(c_0_41, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|r1_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0),esk6_0)), inference(rw,[status(thm)],[c_0_32, c_0_22])).
% 1.00/1.18  cnf(c_0_42, plain, (r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X1)), inference(er,[status(thm)],[c_0_33])).
% 1.00/1.18  cnf(c_0_43, plain, (esk1_2(k1_tarski(X1),X2)=X1|r1_tarski(k1_tarski(X1),X2)), inference(er,[status(thm)],[c_0_34])).
% 1.00/1.18  cnf(c_0_44, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_19, c_0_35])).
% 1.00/1.18  cnf(c_0_45, negated_conjecture, (~r2_hidden(esk4_0,esk6_0)|~r2_hidden(esk5_0,esk6_0)|~r1_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0),esk6_0)), inference(rw,[status(thm)],[c_0_36, c_0_22])).
% 1.00/1.18  cnf(c_0_46, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 1.00/1.18  cnf(c_0_47, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|r2_hidden(X1,esk6_0)|~r2_hidden(X1,k1_enumset1(esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.00/1.18  cnf(c_0_48, plain, (r2_hidden(X1,k1_enumset1(X2,X3,X1))), inference(er,[status(thm)],[c_0_42])).
% 1.00/1.18  cnf(c_0_49, plain, (X1=X2|X3!=k1_tarski(X2)|~r1_tarski(k1_tarski(X1),X3)), inference(spm,[status(thm)],[c_0_25, c_0_39])).
% 1.00/1.18  cnf(c_0_50, plain, (r2_hidden(X1,k1_tarski(X1))|r1_tarski(k1_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_26, c_0_43])).
% 1.00/1.18  cnf(c_0_51, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.00/1.18  cnf(c_0_52, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_44])).
% 1.00/1.18  cnf(c_0_53, negated_conjecture, (~r2_hidden(esk5_0,esk6_0)|~r1_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])])).
% 1.00/1.18  cnf(c_0_54, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 1.00/1.18  cnf(c_0_55, plain, (X1=X2|r2_hidden(X1,k1_tarski(X1))|X3!=k1_tarski(X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.00/1.18  cnf(c_0_56, plain, (r1_tarski(k1_tarski(X1),k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.00/1.18  cnf(c_0_57, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.00/1.18  cnf(c_0_58, negated_conjecture, (~r1_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54])])).
% 1.00/1.18  cnf(c_0_59, plain, (X1=X2|r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[c_0_55])).
% 1.00/1.18  fof(c_0_60, plain, ![X46, X47, X48]:(~r1_tarski(k1_tarski(X46),k2_tarski(X47,X48))|X46=X47|X46=X48), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_zfmisc_1])])).
% 1.00/1.18  cnf(c_0_61, negated_conjecture, (r1_tarski(k1_tarski(esk5_0),k2_xboole_0(esk6_0,X1))), inference(spm,[status(thm)],[c_0_56, c_0_54])).
% 1.00/1.18  cnf(c_0_62, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_44])).
% 1.00/1.18  cnf(c_0_63, plain, (r2_hidden(X1,X2)|X2!=k1_tarski(X1)), inference(er,[status(thm)],[c_0_57])).
% 1.00/1.18  cnf(c_0_64, negated_conjecture, (r2_hidden(X1,k1_tarski(X1))|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 1.00/1.18  cnf(c_0_65, negated_conjecture, (r1_tarski(k1_tarski(esk4_0),esk6_0)), inference(spm,[status(thm)],[c_0_51, c_0_46])).
% 1.00/1.18  cnf(c_0_66, plain, (X1=X2|X1=X3|~r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.00/1.18  cnf(c_0_67, negated_conjecture, (r1_tarski(k1_tarski(esk5_0),X1)|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_20])).
% 1.00/1.18  cnf(c_0_68, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X4)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_40, c_0_62])).
% 1.00/1.18  cnf(c_0_69, plain, (r1_tarski(k1_tarski(X1),X2)|X2!=k1_tarski(X1)), inference(spm,[status(thm)],[c_0_51, c_0_63])).
% 1.00/1.18  cnf(c_0_70, negated_conjecture, (r2_hidden(esk6_0,k1_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_64, c_0_35])).
% 1.00/1.18  cnf(c_0_71, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.00/1.18  cnf(c_0_72, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.00/1.18  cnf(c_0_73, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,k1_tarski(esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_65])).
% 1.00/1.18  cnf(c_0_74, plain, (X1=X3|X1=X2|~r1_tarski(k1_tarski(X1),k1_enumset1(X2,X2,X3))), inference(rw,[status(thm)],[c_0_66, c_0_22])).
% 1.00/1.18  cnf(c_0_75, plain, (r1_tarski(k1_tarski(esk1_2(X1,X2)),X1)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_51, c_0_26])).
% 1.00/1.18  cnf(c_0_76, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_tarski(esk5_0))|~r1_tarski(esk6_0,X2)), inference(spm,[status(thm)],[c_0_40, c_0_67])).
% 1.00/1.18  cnf(c_0_77, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|X2!=k1_tarski(X4)|~r2_hidden(X1,k1_tarski(X4))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 1.00/1.18  cnf(c_0_78, negated_conjecture, (r2_hidden(X1,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_70, c_0_59])).
% 1.00/1.18  cnf(c_0_79, plain, (r2_hidden(X1,X2)|X2!=k1_enumset1(X1,X3,X4)), inference(er,[status(thm)],[c_0_71])).
% 1.00/1.18  cnf(c_0_80, negated_conjecture, (r1_tarski(X1,esk6_0)|~r2_hidden(esk1_2(X1,esk6_0),k1_tarski(esk4_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 1.00/1.18  cnf(c_0_81, plain, (esk1_2(k1_enumset1(X1,X1,X2),X3)=X1|esk1_2(k1_enumset1(X1,X1,X2),X3)=X2|r1_tarski(k1_enumset1(X1,X1,X2),X3)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 1.00/1.18  cnf(c_0_82, negated_conjecture, (r2_hidden(X1,X2)|k1_tarski(esk5_0)!=k1_tarski(X1)|~r1_tarski(esk6_0,X2)), inference(spm,[status(thm)],[c_0_76, c_0_63])).
% 1.00/1.18  cnf(c_0_83, negated_conjecture, (r2_hidden(X1,k2_xboole_0(X2,X3))|X2!=k1_tarski(X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 1.00/1.18  cnf(c_0_84, plain, (r2_hidden(X1,k1_enumset1(X1,X2,X3))), inference(er,[status(thm)],[c_0_79])).
% 1.00/1.18  cnf(c_0_85, negated_conjecture, (esk1_2(k1_enumset1(X1,X1,X2),esk6_0)=X1|r1_tarski(k1_enumset1(X1,X1,X2),esk6_0)|~r2_hidden(X2,k1_tarski(esk4_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 1.00/1.18  cnf(c_0_86, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk6_0,X2))|k1_tarski(esk5_0)!=k1_tarski(X1)), inference(spm,[status(thm)],[c_0_82, c_0_44])).
% 1.00/1.18  cnf(c_0_87, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_72, c_0_52])).
% 1.00/1.18  cnf(c_0_88, negated_conjecture, (r2_hidden(X1,X2)|X3!=k1_tarski(X1)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_83, c_0_20])).
% 1.00/1.18  cnf(c_0_89, plain, (r1_tarski(k1_tarski(X1),k1_enumset1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_51, c_0_84])).
% 1.00/1.18  cnf(c_0_90, negated_conjecture, (r1_tarski(k1_enumset1(X1,X1,X2),esk6_0)|~r2_hidden(X2,k1_tarski(esk4_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_72, c_0_85])).
% 1.00/1.18  cnf(c_0_91, negated_conjecture, (r2_hidden(esk5_0,k2_xboole_0(esk6_0,X1))), inference(er,[status(thm)],[c_0_86])).
% 1.00/1.18  cnf(c_0_92, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_87, c_0_20])).
% 1.00/1.18  cnf(c_0_93, negated_conjecture, (r2_hidden(X1,k1_enumset1(X2,X3,X4))|k1_tarski(X2)!=k1_tarski(X1)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 1.00/1.18  cnf(c_0_94, negated_conjecture, (r1_tarski(k1_enumset1(X1,X1,esk4_0),esk6_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_90, c_0_78])).
% 1.00/1.18  cnf(c_0_95, negated_conjecture, (r2_hidden(esk5_0,X1)|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_91, c_0_20])).
% 1.00/1.18  cnf(c_0_96, negated_conjecture, (r1_tarski(X1,X2)|k1_tarski(X3)!=k1_tarski(esk1_2(X1,X2))|~r1_tarski(k1_enumset1(X3,X4,X5),X2)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 1.00/1.18  cnf(c_0_97, negated_conjecture, (r1_tarski(k1_enumset1(esk5_0,esk5_0,esk4_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_35])])).
% 1.00/1.18  cnf(c_0_98, negated_conjecture, (r1_tarski(X1,esk6_0)|k1_tarski(esk1_2(X1,esk6_0))!=k1_tarski(esk5_0)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 1.00/1.18  cnf(c_0_99, plain, (esk1_2(k1_enumset1(X1,X1,X2),X3)=X2|r1_tarski(k1_enumset1(X1,X1,X2),X3)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_72, c_0_81])).
% 1.00/1.18  cnf(c_0_100, negated_conjecture, (r1_tarski(k1_enumset1(X1,X1,X2),esk6_0)|k1_tarski(X2)!=k1_tarski(esk5_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 1.00/1.18  cnf(c_0_101, negated_conjecture, (r1_tarski(k1_enumset1(esk4_0,esk4_0,X1),esk6_0)|k1_tarski(X1)!=k1_tarski(esk5_0)), inference(spm,[status(thm)],[c_0_100, c_0_46])).
% 1.00/1.18  cnf(c_0_102, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_101]), c_0_58]), ['proof']).
% 1.00/1.18  # SZS output end CNFRefutation
% 1.00/1.18  # Proof object total steps             : 103
% 1.00/1.18  # Proof object clause steps            : 80
% 1.00/1.18  # Proof object formula steps           : 23
% 1.00/1.18  # Proof object conjectures             : 40
% 1.00/1.18  # Proof object clause conjectures      : 37
% 1.00/1.18  # Proof object formula conjectures     : 3
% 1.00/1.18  # Proof object initial clauses used    : 18
% 1.00/1.18  # Proof object initial formulas used   : 11
% 1.00/1.18  # Proof object generating inferences   : 51
% 1.00/1.18  # Proof object simplifying inferences  : 17
% 1.00/1.18  # Training examples: 0 positive, 0 negative
% 1.00/1.18  # Parsed axioms                        : 12
% 1.00/1.18  # Removed by relevancy pruning/SinE    : 0
% 1.00/1.18  # Initial clauses                      : 29
% 1.00/1.18  # Removed in clause preprocessing      : 1
% 1.00/1.18  # Initial clauses in saturation        : 28
% 1.00/1.18  # Processed clauses                    : 7319
% 1.00/1.18  # ...of these trivial                  : 90
% 1.00/1.18  # ...subsumed                          : 5203
% 1.00/1.18  # ...remaining for further processing  : 2026
% 1.00/1.18  # Other redundant clauses eliminated   : 692
% 1.00/1.18  # Clauses deleted for lack of memory   : 0
% 1.00/1.18  # Backward-subsumed                    : 46
% 1.00/1.18  # Backward-rewritten                   : 66
% 1.00/1.18  # Generated clauses                    : 49490
% 1.00/1.18  # ...of the previous two non-trivial   : 46391
% 1.00/1.18  # Contextual simplify-reflections      : 8
% 1.00/1.18  # Paramodulations                      : 48608
% 1.00/1.18  # Factorizations                       : 122
% 1.00/1.18  # Equation resolutions                 : 760
% 1.00/1.18  # Propositional unsat checks           : 0
% 1.00/1.18  #    Propositional check models        : 0
% 1.00/1.18  #    Propositional check unsatisfiable : 0
% 1.00/1.18  #    Propositional clauses             : 0
% 1.00/1.18  #    Propositional clauses after purity: 0
% 1.00/1.18  #    Propositional unsat core size     : 0
% 1.00/1.18  #    Propositional preprocessing time  : 0.000
% 1.00/1.18  #    Propositional encoding time       : 0.000
% 1.00/1.18  #    Propositional solver time         : 0.000
% 1.00/1.18  #    Success case prop preproc time    : 0.000
% 1.00/1.18  #    Success case prop encoding time   : 0.000
% 1.00/1.18  #    Success case prop solver time     : 0.000
% 1.00/1.18  # Current number of processed clauses  : 1881
% 1.00/1.18  #    Positive orientable unit clauses  : 41
% 1.00/1.18  #    Positive unorientable unit clauses: 0
% 1.00/1.18  #    Negative unit clauses             : 4
% 1.00/1.18  #    Non-unit-clauses                  : 1836
% 1.00/1.18  # Current number of unprocessed clauses: 35934
% 1.00/1.18  # ...number of literals in the above   : 158716
% 1.00/1.18  # Current number of archived formulas  : 0
% 1.00/1.18  # Current number of archived clauses   : 140
% 1.00/1.18  # Clause-clause subsumption calls (NU) : 1213337
% 1.00/1.18  # Rec. Clause-clause subsumption calls : 641818
% 1.00/1.18  # Non-unit clause-clause subsumptions  : 4977
% 1.00/1.18  # Unit Clause-clause subsumption calls : 1922
% 1.00/1.18  # Rewrite failures with RHS unbound    : 0
% 1.00/1.18  # BW rewrite match attempts            : 167
% 1.00/1.18  # BW rewrite match successes           : 16
% 1.00/1.18  # Condensation attempts                : 0
% 1.00/1.18  # Condensation successes               : 0
% 1.00/1.18  # Termbank termtop insertions          : 651765
% 1.00/1.18  
% 1.00/1.18  # -------------------------------------------------
% 1.00/1.18  # User time                : 0.813 s
% 1.00/1.18  # System time              : 0.026 s
% 1.00/1.18  # Total time               : 0.839 s
% 1.00/1.18  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
