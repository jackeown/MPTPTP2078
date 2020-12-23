%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:13 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 (1861 expanded)
%              Number of clauses        :   64 ( 833 expanded)
%              Number of leaves         :    8 ( 489 expanded)
%              Depth                    :   25
%              Number of atoms          :  200 (4229 expanded)
%              Number of equality atoms :   94 (2869 expanded)
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

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t129_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))
    <=> ( r2_hidden(X1,X3)
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(c_0_8,plain,(
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

fof(c_0_9,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_10,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( X3 = k1_tarski(k4_tarski(X1,X2))
         => ( k1_relat_1(X3) = k1_tarski(X1)
            & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_relat_1])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & esk10_0 = k1_tarski(k4_tarski(esk8_0,esk9_0))
    & ( k1_relat_1(esk10_0) != k1_tarski(esk8_0)
      | k2_relat_1(esk10_0) != k1_tarski(esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_16,plain,(
    ! [X33,X34,X35,X37,X38,X39,X40,X42] :
      ( ( ~ r2_hidden(X35,X34)
        | r2_hidden(k4_tarski(esk5_3(X33,X34,X35),X35),X33)
        | X34 != k2_relat_1(X33) )
      & ( ~ r2_hidden(k4_tarski(X38,X37),X33)
        | r2_hidden(X37,X34)
        | X34 != k2_relat_1(X33) )
      & ( ~ r2_hidden(esk6_2(X39,X40),X40)
        | ~ r2_hidden(k4_tarski(X42,esk6_2(X39,X40)),X39)
        | X40 = k2_relat_1(X39) )
      & ( r2_hidden(esk6_2(X39,X40),X40)
        | r2_hidden(k4_tarski(esk7_2(X39,X40),esk6_2(X39,X40)),X39)
        | X40 = k2_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk10_0 = k1_tarski(k4_tarski(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])])).

cnf(c_0_23,negated_conjecture,
    ( esk10_0 = k1_enumset1(k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_13]),c_0_14])).

cnf(c_0_24,plain,
    ( X2 = k1_enumset1(X1,X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_13]),c_0_14])).

cnf(c_0_25,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k1_enumset1(X1,X1,X1)
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_13]),c_0_14])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk9_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(esk10_0) != k1_tarski(esk8_0)
    | k2_relat_1(esk10_0) != k1_tarski(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( X1 = k1_enumset1(X2,X2,X2)
    | r2_hidden(esk1_2(X2,X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk9_0,k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_31,plain,(
    ! [X22,X23,X24,X26,X27,X28,X29,X31] :
      ( ( ~ r2_hidden(X24,X23)
        | r2_hidden(k4_tarski(X24,esk2_3(X22,X23,X24)),X22)
        | X23 != k1_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(X26,X27),X22)
        | r2_hidden(X26,X23)
        | X23 != k1_relat_1(X22) )
      & ( ~ r2_hidden(esk3_2(X28,X29),X29)
        | ~ r2_hidden(k4_tarski(esk3_2(X28,X29),X31),X28)
        | X29 = k1_relat_1(X28) )
      & ( r2_hidden(esk3_2(X28,X29),X29)
        | r2_hidden(k4_tarski(esk3_2(X28,X29),esk4_2(X28,X29)),X28)
        | X29 = k1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_32,plain,(
    ! [X15,X16,X17,X18] :
      ( ( r2_hidden(X15,X17)
        | ~ r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,k1_tarski(X18))) )
      & ( X16 = X18
        | ~ r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,k1_tarski(X18))) )
      & ( ~ r2_hidden(X15,X17)
        | X16 != X18
        | r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,k1_tarski(X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).

fof(c_0_33,plain,(
    ! [X19,X20,X21] :
      ( k2_zfmisc_1(k1_tarski(X19),k2_tarski(X20,X21)) = k2_tarski(k4_tarski(X19,X20),k4_tarski(X19,X21))
      & k2_zfmisc_1(k2_tarski(X19,X20),k1_tarski(X21)) = k2_tarski(k4_tarski(X19,X21),k4_tarski(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(esk10_0) != k1_enumset1(esk8_0,esk8_0,esk8_0)
    | k2_relat_1(esk10_0) != k1_enumset1(esk9_0,esk9_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_13]),c_0_13]),c_0_14]),c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( k1_enumset1(esk9_0,esk9_0,esk9_0) = k2_relat_1(esk10_0)
    | r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))
    | k1_enumset1(esk8_0,esk8_0,esk8_0) != k1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_enumset1(X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_13]),c_0_14])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3)) = k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_13]),c_0_14]),c_0_14]),c_0_14])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( esk1_2(esk8_0,k1_relat_1(esk10_0)) = esk8_0
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))
    | r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_25])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk8_0,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_27])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k1_enumset1(k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X5,X2))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_44]),c_0_45])]),c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( X1 = esk9_0
    | ~ r2_hidden(k4_tarski(X2,X1),esk10_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_23])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0)
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( esk1_2(esk9_0,k2_relat_1(esk10_0)) = esk9_0
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_52,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_53,negated_conjecture,
    ( k1_enumset1(esk9_0,esk9_0,esk9_0) = k2_relat_1(esk10_0)
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_51]),c_0_30])])).

cnf(c_0_54,negated_conjecture,
    ( k1_enumset1(esk8_0,esk8_0,esk8_0) = k1_relat_1(esk10_0)
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_45])).

cnf(c_0_55,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_56,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_53]),c_0_54])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k1_tarski(X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_59,plain,
    ( X1 = X3
    | X2 != k1_enumset1(X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_13]),c_0_14])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk2_3(esk10_0,k1_relat_1(esk10_0),esk1_2(esk8_0,k1_relat_1(esk10_0)))),esk10_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k1_enumset1(X4,X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_13]),c_0_14])).

cnf(c_0_62,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( esk2_3(esk10_0,k1_relat_1(esk10_0),esk1_2(esk8_0,k1_relat_1(esk10_0))) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_60])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X3))
    | ~ r2_hidden(k4_tarski(X1,X4),k1_enumset1(k4_tarski(X2,X5),k4_tarski(X2,X5),k4_tarski(X3,X5))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_42])).

cnf(c_0_65,negated_conjecture,
    ( X1 = k4_tarski(esk8_0,esk9_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_23])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk9_0),esk10_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(X1,k1_enumset1(esk8_0,esk8_0,esk8_0))
    | ~ r2_hidden(k4_tarski(X1,X2),esk10_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_23])).

cnf(c_0_68,negated_conjecture,
    ( k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk9_0) = k4_tarski(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_69,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_enumset1(esk8_0,esk8_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_27])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_2(X1,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk6_2(X1,k1_enumset1(esk9_0,esk9_0,esk9_0))),X1)
    | r2_hidden(esk6_2(X1,k1_enumset1(esk9_0,esk9_0,esk9_0)),k1_enumset1(esk9_0,esk9_0,esk9_0))
    | k1_enumset1(esk8_0,esk8_0,esk8_0) != k1_relat_1(esk10_0)
    | k2_relat_1(X1) != k2_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( esk1_2(esk8_0,k1_relat_1(esk10_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0))),esk10_0)
    | r2_hidden(esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),k1_enumset1(esk9_0,esk9_0,esk9_0))
    | k1_enumset1(esk8_0,esk8_0,esk8_0) != k1_relat_1(esk10_0) ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( k1_enumset1(esk8_0,esk8_0,esk8_0) = k1_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_72]),c_0_45])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0))),esk10_0)
    | r2_hidden(esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),k1_enumset1(esk9_0,esk9_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])])).

cnf(c_0_76,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk6_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk6_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_77,negated_conjecture,
    ( esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)) = esk9_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_75]),c_0_62])).

cnf(c_0_78,negated_conjecture,
    ( k1_enumset1(esk9_0,esk9_0,esk9_0) != k2_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_74])])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk9_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_22])]),c_0_78])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_27,c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:32:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.53  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.53  # and selection function SelectNegativeLiterals.
% 0.20/0.53  #
% 0.20/0.53  # Preprocessing time       : 0.028 s
% 0.20/0.53  # Presaturation interreduction done
% 0.20/0.53  
% 0.20/0.53  # Proof found!
% 0.20/0.53  # SZS status Theorem
% 0.20/0.53  # SZS output start CNFRefutation
% 0.20/0.53  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.53  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.53  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.53  fof(t23_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relat_1)).
% 0.20/0.53  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.20/0.53  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.20/0.53  fof(t129_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))<=>(r2_hidden(X1,X3)&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 0.20/0.53  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.20/0.53  fof(c_0_8, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.53  fof(c_0_9, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.53  fof(c_0_10, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.53  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2))))), inference(assume_negation,[status(cth)],[t23_relat_1])).
% 0.20/0.53  cnf(c_0_12, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.53  cnf(c_0_13, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.53  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.53  fof(c_0_15, negated_conjecture, (v1_relat_1(esk10_0)&(esk10_0=k1_tarski(k4_tarski(esk8_0,esk9_0))&(k1_relat_1(esk10_0)!=k1_tarski(esk8_0)|k2_relat_1(esk10_0)!=k1_tarski(esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.20/0.53  fof(c_0_16, plain, ![X33, X34, X35, X37, X38, X39, X40, X42]:(((~r2_hidden(X35,X34)|r2_hidden(k4_tarski(esk5_3(X33,X34,X35),X35),X33)|X34!=k2_relat_1(X33))&(~r2_hidden(k4_tarski(X38,X37),X33)|r2_hidden(X37,X34)|X34!=k2_relat_1(X33)))&((~r2_hidden(esk6_2(X39,X40),X40)|~r2_hidden(k4_tarski(X42,esk6_2(X39,X40)),X39)|X40=k2_relat_1(X39))&(r2_hidden(esk6_2(X39,X40),X40)|r2_hidden(k4_tarski(esk7_2(X39,X40),esk6_2(X39,X40)),X39)|X40=k2_relat_1(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.20/0.53  cnf(c_0_17, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.20/0.53  cnf(c_0_18, negated_conjecture, (esk10_0=k1_tarski(k4_tarski(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.53  cnf(c_0_19, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.53  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.53  cnf(c_0_21, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.53  cnf(c_0_22, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])])).
% 0.20/0.53  cnf(c_0_23, negated_conjecture, (esk10_0=k1_enumset1(k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_13]), c_0_14])).
% 0.20/0.53  cnf(c_0_24, plain, (X2=k1_enumset1(X1,X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_13]), c_0_14])).
% 0.20/0.53  cnf(c_0_25, plain, (esk1_2(X1,X2)=X1|X2=k1_enumset1(X1,X1,X1)|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_13]), c_0_14])).
% 0.20/0.53  cnf(c_0_26, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_21])).
% 0.20/0.53  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk9_0),esk10_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.53  cnf(c_0_28, negated_conjecture, (k1_relat_1(esk10_0)!=k1_tarski(esk8_0)|k2_relat_1(esk10_0)!=k1_tarski(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.53  cnf(c_0_29, plain, (X1=k1_enumset1(X2,X2,X2)|r2_hidden(esk1_2(X2,X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.53  cnf(c_0_30, negated_conjecture, (r2_hidden(esk9_0,k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.53  fof(c_0_31, plain, ![X22, X23, X24, X26, X27, X28, X29, X31]:(((~r2_hidden(X24,X23)|r2_hidden(k4_tarski(X24,esk2_3(X22,X23,X24)),X22)|X23!=k1_relat_1(X22))&(~r2_hidden(k4_tarski(X26,X27),X22)|r2_hidden(X26,X23)|X23!=k1_relat_1(X22)))&((~r2_hidden(esk3_2(X28,X29),X29)|~r2_hidden(k4_tarski(esk3_2(X28,X29),X31),X28)|X29=k1_relat_1(X28))&(r2_hidden(esk3_2(X28,X29),X29)|r2_hidden(k4_tarski(esk3_2(X28,X29),esk4_2(X28,X29)),X28)|X29=k1_relat_1(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.20/0.53  fof(c_0_32, plain, ![X15, X16, X17, X18]:(((r2_hidden(X15,X17)|~r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,k1_tarski(X18))))&(X16=X18|~r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,k1_tarski(X18)))))&(~r2_hidden(X15,X17)|X16!=X18|r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(X17,k1_tarski(X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).
% 0.20/0.53  fof(c_0_33, plain, ![X19, X20, X21]:(k2_zfmisc_1(k1_tarski(X19),k2_tarski(X20,X21))=k2_tarski(k4_tarski(X19,X20),k4_tarski(X19,X21))&k2_zfmisc_1(k2_tarski(X19,X20),k1_tarski(X21))=k2_tarski(k4_tarski(X19,X21),k4_tarski(X20,X21))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.20/0.53  cnf(c_0_34, negated_conjecture, (k1_relat_1(esk10_0)!=k1_enumset1(esk8_0,esk8_0,esk8_0)|k2_relat_1(esk10_0)!=k1_enumset1(esk9_0,esk9_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_13]), c_0_13]), c_0_14]), c_0_14])).
% 0.20/0.53  cnf(c_0_35, negated_conjecture, (k1_enumset1(esk9_0,esk9_0,esk9_0)=k2_relat_1(esk10_0)|r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.53  cnf(c_0_36, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.53  cnf(c_0_37, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.53  cnf(c_0_38, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.53  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))|k1_enumset1(esk8_0,esk8_0,esk8_0)!=k1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.53  cnf(c_0_40, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_36])).
% 0.20/0.53  cnf(c_0_41, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_enumset1(X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_13]), c_0_14])).
% 0.20/0.53  cnf(c_0_42, plain, (k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3))=k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_13]), c_0_14]), c_0_14]), c_0_14])).
% 0.20/0.53  cnf(c_0_43, plain, (r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.53  cnf(c_0_44, negated_conjecture, (esk1_2(esk8_0,k1_relat_1(esk10_0))=esk8_0|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))|r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_25])])).
% 0.20/0.53  cnf(c_0_45, negated_conjecture, (r2_hidden(esk8_0,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_40, c_0_27])).
% 0.20/0.53  cnf(c_0_46, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k1_enumset1(k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X5,X2)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.53  cnf(c_0_47, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_43])).
% 0.20/0.53  cnf(c_0_48, negated_conjecture, (r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_44]), c_0_45])]), c_0_39])).
% 0.20/0.53  cnf(c_0_49, negated_conjecture, (X1=esk9_0|~r2_hidden(k4_tarski(X2,X1),esk10_0)), inference(spm,[status(thm)],[c_0_46, c_0_23])).
% 0.20/0.53  cnf(c_0_50, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0)|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.53  cnf(c_0_51, negated_conjecture, (esk1_2(esk9_0,k2_relat_1(esk10_0))=esk9_0|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.53  cnf(c_0_52, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.53  cnf(c_0_53, negated_conjecture, (k1_enumset1(esk9_0,esk9_0,esk9_0)=k2_relat_1(esk10_0)|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_51]), c_0_30])])).
% 0.20/0.53  cnf(c_0_54, negated_conjecture, (k1_enumset1(esk8_0,esk8_0,esk8_0)=k1_relat_1(esk10_0)|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_29, c_0_45])).
% 0.20/0.53  cnf(c_0_55, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.53  cnf(c_0_56, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_52])).
% 0.20/0.53  cnf(c_0_57, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_53]), c_0_54])).
% 0.20/0.53  cnf(c_0_58, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k1_tarski(X4)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.53  cnf(c_0_59, plain, (X1=X3|X2!=k1_enumset1(X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_13]), c_0_14])).
% 0.20/0.53  cnf(c_0_60, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk2_3(esk10_0,k1_relat_1(esk10_0),esk1_2(esk8_0,k1_relat_1(esk10_0)))),esk10_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.53  cnf(c_0_61, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k1_enumset1(X4,X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_13]), c_0_14])).
% 0.20/0.53  cnf(c_0_62, plain, (X1=X2|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(er,[status(thm)],[c_0_59])).
% 0.20/0.53  cnf(c_0_63, negated_conjecture, (esk2_3(esk10_0,k1_relat_1(esk10_0),esk1_2(esk8_0,k1_relat_1(esk10_0)))=esk9_0), inference(spm,[status(thm)],[c_0_49, c_0_60])).
% 0.20/0.53  cnf(c_0_64, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X3))|~r2_hidden(k4_tarski(X1,X4),k1_enumset1(k4_tarski(X2,X5),k4_tarski(X2,X5),k4_tarski(X3,X5)))), inference(spm,[status(thm)],[c_0_61, c_0_42])).
% 0.20/0.53  cnf(c_0_65, negated_conjecture, (X1=k4_tarski(esk8_0,esk9_0)|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_62, c_0_23])).
% 0.20/0.53  cnf(c_0_66, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk9_0),esk10_0)), inference(rw,[status(thm)],[c_0_60, c_0_63])).
% 0.20/0.53  cnf(c_0_67, negated_conjecture, (r2_hidden(X1,k1_enumset1(esk8_0,esk8_0,esk8_0))|~r2_hidden(k4_tarski(X1,X2),esk10_0)), inference(spm,[status(thm)],[c_0_64, c_0_23])).
% 0.20/0.53  cnf(c_0_68, negated_conjecture, (k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk9_0)=k4_tarski(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.53  cnf(c_0_69, plain, (r2_hidden(esk6_2(X1,X2),X2)|r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.53  cnf(c_0_70, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_enumset1(esk8_0,esk8_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_27])])).
% 0.20/0.53  cnf(c_0_71, negated_conjecture, (r2_hidden(k4_tarski(esk7_2(X1,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk6_2(X1,k1_enumset1(esk9_0,esk9_0,esk9_0))),X1)|r2_hidden(esk6_2(X1,k1_enumset1(esk9_0,esk9_0,esk9_0)),k1_enumset1(esk9_0,esk9_0,esk9_0))|k1_enumset1(esk8_0,esk8_0,esk8_0)!=k1_relat_1(esk10_0)|k2_relat_1(X1)!=k2_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_34, c_0_69])).
% 0.20/0.53  cnf(c_0_72, negated_conjecture, (esk1_2(esk8_0,k1_relat_1(esk10_0))=esk8_0), inference(spm,[status(thm)],[c_0_62, c_0_70])).
% 0.20/0.53  cnf(c_0_73, negated_conjecture, (r2_hidden(k4_tarski(esk7_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0))),esk10_0)|r2_hidden(esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),k1_enumset1(esk9_0,esk9_0,esk9_0))|k1_enumset1(esk8_0,esk8_0,esk8_0)!=k1_relat_1(esk10_0)), inference(er,[status(thm)],[c_0_71])).
% 0.20/0.53  cnf(c_0_74, negated_conjecture, (k1_enumset1(esk8_0,esk8_0,esk8_0)=k1_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_72]), c_0_45])])).
% 0.20/0.53  cnf(c_0_75, negated_conjecture, (r2_hidden(k4_tarski(esk7_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0))),esk10_0)|r2_hidden(esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),k1_enumset1(esk9_0,esk9_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74])])).
% 0.20/0.53  cnf(c_0_76, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk6_2(X1,X2),X2)|~r2_hidden(k4_tarski(X3,esk6_2(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.53  cnf(c_0_77, negated_conjecture, (esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0))=esk9_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_75]), c_0_62])).
% 0.20/0.53  cnf(c_0_78, negated_conjecture, (k1_enumset1(esk9_0,esk9_0,esk9_0)!=k2_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_74])])).
% 0.20/0.53  cnf(c_0_79, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk9_0),esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_22])]), c_0_78])).
% 0.20/0.53  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_27, c_0_79]), ['proof']).
% 0.20/0.53  # SZS output end CNFRefutation
% 0.20/0.53  # Proof object total steps             : 81
% 0.20/0.53  # Proof object clause steps            : 64
% 0.20/0.53  # Proof object formula steps           : 17
% 0.20/0.53  # Proof object conjectures             : 36
% 0.20/0.53  # Proof object clause conjectures      : 33
% 0.20/0.53  # Proof object formula conjectures     : 3
% 0.20/0.53  # Proof object initial clauses used    : 17
% 0.20/0.53  # Proof object initial formulas used   : 8
% 0.20/0.53  # Proof object generating inferences   : 28
% 0.20/0.53  # Proof object simplifying inferences  : 50
% 0.20/0.53  # Training examples: 0 positive, 0 negative
% 0.20/0.53  # Parsed axioms                        : 8
% 0.20/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.53  # Initial clauses                      : 22
% 0.20/0.53  # Removed in clause preprocessing      : 2
% 0.20/0.53  # Initial clauses in saturation        : 20
% 0.20/0.53  # Processed clauses                    : 509
% 0.20/0.53  # ...of these trivial                  : 7
% 0.20/0.53  # ...subsumed                          : 120
% 0.20/0.53  # ...remaining for further processing  : 382
% 0.20/0.53  # Other redundant clauses eliminated   : 119
% 0.20/0.53  # Clauses deleted for lack of memory   : 0
% 0.20/0.53  # Backward-subsumed                    : 71
% 0.20/0.53  # Backward-rewritten                   : 107
% 0.20/0.53  # Generated clauses                    : 8811
% 0.20/0.53  # ...of the previous two non-trivial   : 8239
% 0.20/0.53  # Contextual simplify-reflections      : 7
% 0.20/0.53  # Paramodulations                      : 8679
% 0.20/0.53  # Factorizations                       : 11
% 0.20/0.53  # Equation resolutions                 : 120
% 0.20/0.53  # Propositional unsat checks           : 0
% 0.20/0.53  #    Propositional check models        : 0
% 0.20/0.53  #    Propositional check unsatisfiable : 0
% 0.20/0.53  #    Propositional clauses             : 0
% 0.20/0.53  #    Propositional clauses after purity: 0
% 0.20/0.53  #    Propositional unsat core size     : 0
% 0.20/0.53  #    Propositional preprocessing time  : 0.000
% 0.20/0.53  #    Propositional encoding time       : 0.000
% 0.20/0.53  #    Propositional solver time         : 0.000
% 0.20/0.53  #    Success case prop preproc time    : 0.000
% 0.20/0.53  #    Success case prop encoding time   : 0.000
% 0.20/0.53  #    Success case prop solver time     : 0.000
% 0.20/0.53  # Current number of processed clauses  : 175
% 0.20/0.53  #    Positive orientable unit clauses  : 94
% 0.20/0.53  #    Positive unorientable unit clauses: 0
% 0.20/0.53  #    Negative unit clauses             : 2
% 0.20/0.53  #    Non-unit-clauses                  : 79
% 0.20/0.53  # Current number of unprocessed clauses: 7661
% 0.20/0.53  # ...number of literals in the above   : 35336
% 0.20/0.53  # Current number of archived formulas  : 0
% 0.20/0.53  # Current number of archived clauses   : 202
% 0.20/0.53  # Clause-clause subsumption calls (NU) : 5649
% 0.20/0.53  # Rec. Clause-clause subsumption calls : 2661
% 0.20/0.53  # Non-unit clause-clause subsumptions  : 186
% 0.20/0.53  # Unit Clause-clause subsumption calls : 1003
% 0.20/0.53  # Rewrite failures with RHS unbound    : 0
% 0.20/0.53  # BW rewrite match attempts            : 192
% 0.20/0.53  # BW rewrite match successes           : 21
% 0.20/0.53  # Condensation attempts                : 0
% 0.20/0.53  # Condensation successes               : 0
% 0.20/0.53  # Termbank termtop insertions          : 177979
% 0.20/0.53  
% 0.20/0.53  # -------------------------------------------------
% 0.20/0.53  # User time                : 0.172 s
% 0.20/0.53  # System time              : 0.010 s
% 0.20/0.53  # Total time               : 0.183 s
% 0.20/0.53  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
