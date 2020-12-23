%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:12 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 (4888 expanded)
%              Number of clauses        :   64 (1981 expanded)
%              Number of leaves         :    9 (1425 expanded)
%              Depth                    :   28
%              Number of atoms          :  188 (7804 expanded)
%              Number of equality atoms :   91 (5868 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t23_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( X3 = k1_tarski(k4_tarski(X1,X2))
       => ( k1_relat_1(X3) = k1_tarski(X1)
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(t128_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
    <=> ( X1 = X3
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(c_0_9,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( X3 = k1_tarski(k4_tarski(X1,X2))
         => ( k1_relat_1(X3) = k1_tarski(X1)
            & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_relat_1])).

fof(c_0_14,plain,(
    ! [X35,X36,X37,X39,X40,X41,X42,X44] :
      ( ( ~ r2_hidden(X37,X36)
        | r2_hidden(k4_tarski(esk5_3(X35,X36,X37),X37),X35)
        | X36 != k2_relat_1(X35) )
      & ( ~ r2_hidden(k4_tarski(X40,X39),X35)
        | r2_hidden(X39,X36)
        | X36 != k2_relat_1(X35) )
      & ( ~ r2_hidden(esk6_2(X41,X42),X42)
        | ~ r2_hidden(k4_tarski(X44,esk6_2(X41,X42)),X41)
        | X42 = k2_relat_1(X41) )
      & ( r2_hidden(esk6_2(X41,X42),X42)
        | r2_hidden(k4_tarski(esk7_2(X41,X42),esk6_2(X41,X42)),X41)
        | X42 = k2_relat_1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X22,X23] : k2_zfmisc_1(k1_tarski(X22),k1_tarski(X23)) = k1_tarski(k4_tarski(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t35_zfmisc_1])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & esk10_0 = k1_tarski(k4_tarski(esk8_0,esk9_0))
    & ( k1_relat_1(esk10_0) != k1_tarski(esk8_0)
      | k2_relat_1(esk10_0) != k1_tarski(esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( esk10_0 = k1_tarski(k4_tarski(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X18,X19,X20,X21] :
      ( ( X18 = X20
        | ~ r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(k1_tarski(X20),X21)) )
      & ( r2_hidden(X19,X21)
        | ~ r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(k1_tarski(X20),X21)) )
      & ( X18 != X20
        | ~ r2_hidden(X19,X21)
        | r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(k1_tarski(X20),X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])])).

cnf(c_0_28,plain,
    ( k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_16]),c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( esk10_0 = k2_enumset1(k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k2_relat_1(k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k2_zfmisc_1(k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)) = esk10_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk9_0,k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_39,plain,(
    ! [X24,X25,X26,X28,X29,X30,X31,X33] :
      ( ( ~ r2_hidden(X26,X25)
        | r2_hidden(k4_tarski(X26,esk2_3(X24,X25,X26)),X24)
        | X25 != k1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X28,X29),X24)
        | r2_hidden(X28,X25)
        | X25 != k1_relat_1(X24) )
      & ( ~ r2_hidden(esk3_2(X30,X31),X31)
        | ~ r2_hidden(k4_tarski(esk3_2(X30,X31),X33),X30)
        | X31 = k1_relat_1(X30) )
      & ( r2_hidden(esk3_2(X30,X31),X31)
        | r2_hidden(k4_tarski(esk3_2(X30,X31),esk4_2(X30,X31)),X30)
        | X31 = k1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_40,negated_conjecture,
    ( X1 = esk8_0
    | ~ r2_hidden(k4_tarski(X1,X2),esk10_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk9_0),esk9_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( X2 = k2_enumset1(X1,X1,X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_43,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( esk5_3(esk10_0,k2_relat_1(esk10_0),esk9_0) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k1_relat_1(esk10_0) != k1_tarski(esk8_0)
    | k2_relat_1(esk10_0) != k1_tarski(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,plain,
    ( X1 = k2_enumset1(X2,X2,X2,X2)
    | r2_hidden(esk1_2(X2,X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk9_0),esk10_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(esk10_0) != k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)
    | k2_relat_1(esk10_0) != k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0) = k2_relat_1(esk10_0)
    | r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk8_0,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k1_tarski(X4),X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))
    | k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0) != k1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0) = k1_relat_1(esk10_0)
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_52])).

cnf(c_0_56,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k2_enumset1(X4,X4,X4,X4),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))
    | r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))
    | ~ r2_hidden(k4_tarski(X2,X1),esk10_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0)
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_58])).

cnf(c_0_62,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( esk1_2(esk9_0,k2_relat_1(esk10_0)) = esk9_0
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_65,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_66,negated_conjecture,
    ( k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0) = k2_relat_1(esk10_0)
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_64]),c_0_36])])).

cnf(c_0_67,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_66]),c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk2_3(esk10_0,k1_relat_1(esk10_0),esk1_2(esk8_0,k1_relat_1(esk10_0)))),esk10_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( esk1_2(esk8_0,k1_relat_1(esk10_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_69])).

cnf(c_0_71,negated_conjecture,
    ( k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0) = k1_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_70]),c_0_52])])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_71])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_72])).

cnf(c_0_74,plain,
    ( X1 = k4_tarski(X2,X3)
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_28])).

cnf(c_0_75,negated_conjecture,
    ( esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( X1 = k4_tarski(esk8_0,esk9_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_33])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( k4_tarski(esk8_0,esk1_2(esk9_0,k2_relat_1(esk10_0))) = k4_tarski(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_78]),c_0_49])])).

cnf(c_0_80,negated_conjecture,
    ( esk1_2(esk9_0,k2_relat_1(esk10_0)) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_79])).

cnf(c_0_81,negated_conjecture,
    ( k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0) != k2_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_71])])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_80]),c_0_36])]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.50  # and selection function SelectNegativeLiterals.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.028 s
% 0.20/0.50  # Presaturation interreduction done
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.50  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.50  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.50  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.50  fof(t23_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relat_1)).
% 0.20/0.50  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.20/0.50  fof(t35_zfmisc_1, axiom, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 0.20/0.50  fof(t128_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 0.20/0.50  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.20/0.50  fof(c_0_9, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.50  fof(c_0_10, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.50  fof(c_0_11, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.50  fof(c_0_12, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.50  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2))))), inference(assume_negation,[status(cth)],[t23_relat_1])).
% 0.20/0.50  fof(c_0_14, plain, ![X35, X36, X37, X39, X40, X41, X42, X44]:(((~r2_hidden(X37,X36)|r2_hidden(k4_tarski(esk5_3(X35,X36,X37),X37),X35)|X36!=k2_relat_1(X35))&(~r2_hidden(k4_tarski(X40,X39),X35)|r2_hidden(X39,X36)|X36!=k2_relat_1(X35)))&((~r2_hidden(esk6_2(X41,X42),X42)|~r2_hidden(k4_tarski(X44,esk6_2(X41,X42)),X41)|X42=k2_relat_1(X41))&(r2_hidden(esk6_2(X41,X42),X42)|r2_hidden(k4_tarski(esk7_2(X41,X42),esk6_2(X41,X42)),X41)|X42=k2_relat_1(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.20/0.50  cnf(c_0_15, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.50  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.50  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.50  fof(c_0_19, plain, ![X22, X23]:k2_zfmisc_1(k1_tarski(X22),k1_tarski(X23))=k1_tarski(k4_tarski(X22,X23)), inference(variable_rename,[status(thm)],[t35_zfmisc_1])).
% 0.20/0.50  fof(c_0_20, negated_conjecture, (v1_relat_1(esk10_0)&(esk10_0=k1_tarski(k4_tarski(esk8_0,esk9_0))&(k1_relat_1(esk10_0)!=k1_tarski(esk8_0)|k2_relat_1(esk10_0)!=k1_tarski(esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.20/0.50  cnf(c_0_21, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.50  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.20/0.50  cnf(c_0_23, plain, (k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.50  cnf(c_0_24, negated_conjecture, (esk10_0=k1_tarski(k4_tarski(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.50  fof(c_0_25, plain, ![X18, X19, X20, X21]:(((X18=X20|~r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(k1_tarski(X20),X21)))&(r2_hidden(X19,X21)|~r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(k1_tarski(X20),X21))))&(X18!=X20|~r2_hidden(X19,X21)|r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(k1_tarski(X20),X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).
% 0.20/0.50  cnf(c_0_26, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_21])).
% 0.20/0.50  cnf(c_0_27, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])])).
% 0.20/0.50  cnf(c_0_28, plain, (k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_16]), c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_18])).
% 0.20/0.50  cnf(c_0_29, negated_conjecture, (esk10_0=k2_enumset1(k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_16]), c_0_17]), c_0_18])).
% 0.20/0.50  cnf(c_0_30, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.50  cnf(c_0_31, plain, (r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.50  cnf(c_0_32, plain, (r2_hidden(X1,k2_relat_1(k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.20/0.50  cnf(c_0_33, negated_conjecture, (k2_zfmisc_1(k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))=esk10_0), inference(rw,[status(thm)],[c_0_29, c_0_28])).
% 0.20/0.50  cnf(c_0_34, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_16]), c_0_17]), c_0_18])).
% 0.20/0.50  cnf(c_0_35, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_31])).
% 0.20/0.50  cnf(c_0_36, negated_conjecture, (r2_hidden(esk9_0,k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.50  cnf(c_0_37, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  fof(c_0_39, plain, ![X24, X25, X26, X28, X29, X30, X31, X33]:(((~r2_hidden(X26,X25)|r2_hidden(k4_tarski(X26,esk2_3(X24,X25,X26)),X24)|X25!=k1_relat_1(X24))&(~r2_hidden(k4_tarski(X28,X29),X24)|r2_hidden(X28,X25)|X25!=k1_relat_1(X24)))&((~r2_hidden(esk3_2(X30,X31),X31)|~r2_hidden(k4_tarski(esk3_2(X30,X31),X33),X30)|X31=k1_relat_1(X30))&(r2_hidden(esk3_2(X30,X31),X31)|r2_hidden(k4_tarski(esk3_2(X30,X31),esk4_2(X30,X31)),X30)|X31=k1_relat_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.20/0.50  cnf(c_0_40, negated_conjecture, (X1=esk8_0|~r2_hidden(k4_tarski(X1,X2),esk10_0)), inference(spm,[status(thm)],[c_0_34, c_0_33])).
% 0.20/0.50  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk9_0),esk9_0),esk10_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.50  cnf(c_0_42, plain, (X2=k2_enumset1(X1,X1,X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_16]), c_0_17]), c_0_18])).
% 0.20/0.50  cnf(c_0_43, plain, (esk1_2(X1,X2)=X1|X2=k2_enumset1(X1,X1,X1,X1)|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_16]), c_0_17]), c_0_18])).
% 0.20/0.50  cnf(c_0_44, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.50  cnf(c_0_45, negated_conjecture, (esk5_3(esk10_0,k2_relat_1(esk10_0),esk9_0)=esk8_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.50  cnf(c_0_46, negated_conjecture, (k1_relat_1(esk10_0)!=k1_tarski(esk8_0)|k2_relat_1(esk10_0)!=k1_tarski(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.50  cnf(c_0_47, plain, (X1=k2_enumset1(X2,X2,X2,X2)|r2_hidden(esk1_2(X2,X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.50  cnf(c_0_48, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_44])).
% 0.20/0.50  cnf(c_0_49, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk9_0),esk10_0)), inference(rw,[status(thm)],[c_0_41, c_0_45])).
% 0.20/0.50  cnf(c_0_50, negated_conjecture, (k1_relat_1(esk10_0)!=k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)|k2_relat_1(esk10_0)!=k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_18]), c_0_18])).
% 0.20/0.50  cnf(c_0_51, negated_conjecture, (k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)=k2_relat_1(esk10_0)|r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_47, c_0_36])).
% 0.20/0.50  cnf(c_0_52, negated_conjecture, (r2_hidden(esk8_0,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.50  cnf(c_0_53, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k1_tarski(X4),X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.50  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))|k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)!=k1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.50  cnf(c_0_55, negated_conjecture, (k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)=k1_relat_1(esk10_0)|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_47, c_0_52])).
% 0.20/0.50  cnf(c_0_56, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_57, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k2_enumset1(X4,X4,X4,X4),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_16]), c_0_17]), c_0_18])).
% 0.20/0.50  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))|r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.50  cnf(c_0_59, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_16]), c_0_17]), c_0_18])).
% 0.20/0.50  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))|~r2_hidden(k4_tarski(X2,X1),esk10_0)), inference(spm,[status(thm)],[c_0_57, c_0_33])).
% 0.20/0.50  cnf(c_0_61, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0)|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_35, c_0_58])).
% 0.20/0.50  cnf(c_0_62, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_59])).
% 0.20/0.50  cnf(c_0_63, negated_conjecture, (r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.50  cnf(c_0_64, negated_conjecture, (esk1_2(esk9_0,k2_relat_1(esk10_0))=esk9_0|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.50  cnf(c_0_65, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.50  cnf(c_0_66, negated_conjecture, (k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)=k2_relat_1(esk10_0)|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_64]), c_0_36])])).
% 0.20/0.50  cnf(c_0_67, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_65])).
% 0.20/0.50  cnf(c_0_68, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_66]), c_0_55])).
% 0.20/0.50  cnf(c_0_69, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk2_3(esk10_0,k1_relat_1(esk10_0),esk1_2(esk8_0,k1_relat_1(esk10_0)))),esk10_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.50  cnf(c_0_70, negated_conjecture, (esk1_2(esk8_0,k1_relat_1(esk10_0))=esk8_0), inference(spm,[status(thm)],[c_0_40, c_0_69])).
% 0.20/0.50  cnf(c_0_71, negated_conjecture, (k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)=k1_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_70]), c_0_52])])).
% 0.20/0.50  cnf(c_0_72, negated_conjecture, (r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_71])])).
% 0.20/0.50  cnf(c_0_73, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0)), inference(spm,[status(thm)],[c_0_35, c_0_72])).
% 0.20/0.50  cnf(c_0_74, plain, (X1=k4_tarski(X2,X3)|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))), inference(spm,[status(thm)],[c_0_62, c_0_28])).
% 0.20/0.50  cnf(c_0_75, negated_conjecture, (esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0)))=esk8_0), inference(spm,[status(thm)],[c_0_40, c_0_73])).
% 0.20/0.50  cnf(c_0_76, negated_conjecture, (X1=k4_tarski(esk8_0,esk9_0)|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_74, c_0_33])).
% 0.20/0.50  cnf(c_0_77, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0)), inference(rw,[status(thm)],[c_0_73, c_0_75])).
% 0.20/0.50  cnf(c_0_78, negated_conjecture, (k4_tarski(esk8_0,esk1_2(esk9_0,k2_relat_1(esk10_0)))=k4_tarski(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.50  cnf(c_0_79, negated_conjecture, (r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_78]), c_0_49])])).
% 0.20/0.50  cnf(c_0_80, negated_conjecture, (esk1_2(esk9_0,k2_relat_1(esk10_0))=esk9_0), inference(spm,[status(thm)],[c_0_62, c_0_79])).
% 0.20/0.50  cnf(c_0_81, negated_conjecture, (k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)!=k2_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_71])])).
% 0.20/0.50  cnf(c_0_82, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_80]), c_0_36])]), c_0_81]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 83
% 0.20/0.50  # Proof object clause steps            : 64
% 0.20/0.50  # Proof object formula steps           : 19
% 0.20/0.50  # Proof object conjectures             : 37
% 0.20/0.50  # Proof object clause conjectures      : 34
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 16
% 0.20/0.50  # Proof object initial formulas used   : 9
% 0.20/0.50  # Proof object generating inferences   : 28
% 0.20/0.50  # Proof object simplifying inferences  : 61
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 9
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 22
% 0.20/0.50  # Removed in clause preprocessing      : 3
% 0.20/0.50  # Initial clauses in saturation        : 19
% 0.20/0.50  # Processed clauses                    : 389
% 0.20/0.50  # ...of these trivial                  : 6
% 0.20/0.50  # ...subsumed                          : 79
% 0.20/0.50  # ...remaining for further processing  : 304
% 0.20/0.50  # Other redundant clauses eliminated   : 77
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 82
% 0.20/0.50  # Backward-rewritten                   : 64
% 0.20/0.50  # Generated clauses                    : 6691
% 0.20/0.50  # ...of the previous two non-trivial   : 6383
% 0.20/0.50  # Contextual simplify-reflections      : 6
% 0.20/0.50  # Paramodulations                      : 6614
% 0.20/0.50  # Factorizations                       : 0
% 0.20/0.50  # Equation resolutions                 : 77
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 131
% 0.20/0.50  #    Positive orientable unit clauses  : 40
% 0.20/0.50  #    Positive unorientable unit clauses: 0
% 0.20/0.50  #    Negative unit clauses             : 1
% 0.20/0.50  #    Non-unit-clauses                  : 90
% 0.20/0.50  # Current number of unprocessed clauses: 5835
% 0.20/0.50  # ...number of literals in the above   : 31020
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 169
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 5247
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 1499
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 165
% 0.20/0.50  # Unit Clause-clause subsumption calls : 588
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 49
% 0.20/0.50  # BW rewrite match successes           : 13
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 170184
% 0.20/0.50  
% 0.20/0.50  # -------------------------------------------------
% 0.20/0.50  # User time                : 0.150 s
% 0.20/0.50  # System time              : 0.009 s
% 0.20/0.50  # Total time               : 0.160 s
% 0.20/0.50  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
