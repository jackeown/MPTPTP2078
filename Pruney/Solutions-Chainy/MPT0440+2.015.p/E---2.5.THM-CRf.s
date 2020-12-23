%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:13 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   79 (1119 expanded)
%              Number of clauses        :   62 ( 499 expanded)
%              Number of leaves         :    8 ( 295 expanded)
%              Depth                    :   21
%              Number of atoms          :  198 (2533 expanded)
%              Number of equality atoms :  100 (1724 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t23_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( X3 = k1_tarski(k4_tarski(X1,X2))
       => ( k1_relat_1(X3) = k1_tarski(X1)
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t34_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))
    <=> ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

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
      ( ( X15 = X17
        | ~ r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(k1_tarski(X17),k1_tarski(X18))) )
      & ( X16 = X18
        | ~ r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(k1_tarski(X17),k1_tarski(X18))) )
      & ( X15 != X17
        | X16 != X18
        | r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(k1_tarski(X17),k1_tarski(X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).

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
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k1_tarski(X4),k1_tarski(X2))) ),
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
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k1_enumset1(X4,X4,X4),k1_enumset1(X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_13]),c_0_13]),c_0_14]),c_0_14])).

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
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_47,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k1_enumset1(k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X4,X2))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_44]),c_0_45])]),c_0_39])).

cnf(c_0_50,plain,
    ( X1 = X3
    | X2 != k1_enumset1(X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_13]),c_0_14])).

cnf(c_0_51,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_52,negated_conjecture,
    ( X1 = esk9_0
    | ~ r2_hidden(k4_tarski(X2,X1),esk10_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0)
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( esk1_2(esk9_0,k2_relat_1(esk10_0)) = esk9_0
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_enumset1(X2,X2,X2),k1_enumset1(X4,X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_13]),c_0_13]),c_0_14]),c_0_14])).

cnf(c_0_59,negated_conjecture,
    ( X1 = k4_tarski(esk8_0,esk9_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_23])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk2_3(esk10_0,k1_relat_1(esk10_0),esk8_0)),esk10_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_45])).

cnf(c_0_61,negated_conjecture,
    ( k1_enumset1(esk9_0,esk9_0,esk9_0) = k2_relat_1(esk10_0)
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_57]),c_0_30])])).

cnf(c_0_62,negated_conjecture,
    ( k1_enumset1(esk8_0,esk8_0,esk8_0) = k1_relat_1(esk10_0)
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_45])).

cnf(c_0_63,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k1_enumset1(k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X2,X4))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_42])).

cnf(c_0_64,negated_conjecture,
    ( k4_tarski(esk8_0,esk2_3(esk10_0,k1_relat_1(esk10_0),esk8_0)) = k4_tarski(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_61]),c_0_62])).

cnf(c_0_66,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_67,negated_conjecture,
    ( X1 = esk8_0
    | ~ r2_hidden(k4_tarski(X1,X2),esk10_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_23])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk2_3(esk10_0,k1_relat_1(esk10_0),esk1_2(esk8_0,k1_relat_1(esk10_0)))),esk10_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_2(X1,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk6_2(X1,k1_enumset1(esk9_0,esk9_0,esk9_0))),X1)
    | r2_hidden(esk6_2(X1,k1_enumset1(esk9_0,esk9_0,esk9_0)),k1_enumset1(esk9_0,esk9_0,esk9_0))
    | k1_enumset1(esk8_0,esk8_0,esk8_0) != k1_relat_1(esk10_0)
    | k2_relat_1(X1) != k2_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( esk1_2(esk8_0,k1_relat_1(esk10_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0))),esk10_0)
    | r2_hidden(esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),k1_enumset1(esk9_0,esk9_0,esk9_0))
    | k1_enumset1(esk8_0,esk8_0,esk8_0) != k1_relat_1(esk10_0) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( k1_enumset1(esk8_0,esk8_0,esk8_0) = k1_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_70]),c_0_45])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0))),esk10_0)
    | r2_hidden(esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),k1_enumset1(esk9_0,esk9_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])])).

cnf(c_0_74,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk6_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk6_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_75,negated_conjecture,
    ( esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)) = esk9_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_73]),c_0_55])).

cnf(c_0_76,negated_conjecture,
    ( k1_enumset1(esk9_0,esk9_0,esk9_0) != k2_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_72])])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk9_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_22])]),c_0_76])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_27,c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:35:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.41  # and selection function SelectNegativeLiterals.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.028 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.41  fof(t23_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relat_1)).
% 0.19/0.41  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.41  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.19/0.41  fof(t34_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))<=>(X1=X3&X2=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 0.19/0.41  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.19/0.41  fof(c_0_8, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.41  fof(c_0_9, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.41  fof(c_0_10, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.41  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2))))), inference(assume_negation,[status(cth)],[t23_relat_1])).
% 0.19/0.41  cnf(c_0_12, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_13, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.41  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.41  fof(c_0_15, negated_conjecture, (v1_relat_1(esk10_0)&(esk10_0=k1_tarski(k4_tarski(esk8_0,esk9_0))&(k1_relat_1(esk10_0)!=k1_tarski(esk8_0)|k2_relat_1(esk10_0)!=k1_tarski(esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.19/0.41  fof(c_0_16, plain, ![X33, X34, X35, X37, X38, X39, X40, X42]:(((~r2_hidden(X35,X34)|r2_hidden(k4_tarski(esk5_3(X33,X34,X35),X35),X33)|X34!=k2_relat_1(X33))&(~r2_hidden(k4_tarski(X38,X37),X33)|r2_hidden(X37,X34)|X34!=k2_relat_1(X33)))&((~r2_hidden(esk6_2(X39,X40),X40)|~r2_hidden(k4_tarski(X42,esk6_2(X39,X40)),X39)|X40=k2_relat_1(X39))&(r2_hidden(esk6_2(X39,X40),X40)|r2_hidden(k4_tarski(esk7_2(X39,X40),esk6_2(X39,X40)),X39)|X40=k2_relat_1(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.41  cnf(c_0_17, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.19/0.41  cnf(c_0_18, negated_conjecture, (esk10_0=k1_tarski(k4_tarski(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_19, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_21, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_22, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])])).
% 0.19/0.41  cnf(c_0_23, negated_conjecture, (esk10_0=k1_enumset1(k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_13]), c_0_14])).
% 0.19/0.41  cnf(c_0_24, plain, (X2=k1_enumset1(X1,X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_13]), c_0_14])).
% 0.19/0.41  cnf(c_0_25, plain, (esk1_2(X1,X2)=X1|X2=k1_enumset1(X1,X1,X1)|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_13]), c_0_14])).
% 0.19/0.41  cnf(c_0_26, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk9_0),esk10_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.41  cnf(c_0_28, negated_conjecture, (k1_relat_1(esk10_0)!=k1_tarski(esk8_0)|k2_relat_1(esk10_0)!=k1_tarski(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_29, plain, (X1=k1_enumset1(X2,X2,X2)|r2_hidden(esk1_2(X2,X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (r2_hidden(esk9_0,k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.41  fof(c_0_31, plain, ![X22, X23, X24, X26, X27, X28, X29, X31]:(((~r2_hidden(X24,X23)|r2_hidden(k4_tarski(X24,esk2_3(X22,X23,X24)),X22)|X23!=k1_relat_1(X22))&(~r2_hidden(k4_tarski(X26,X27),X22)|r2_hidden(X26,X23)|X23!=k1_relat_1(X22)))&((~r2_hidden(esk3_2(X28,X29),X29)|~r2_hidden(k4_tarski(esk3_2(X28,X29),X31),X28)|X29=k1_relat_1(X28))&(r2_hidden(esk3_2(X28,X29),X29)|r2_hidden(k4_tarski(esk3_2(X28,X29),esk4_2(X28,X29)),X28)|X29=k1_relat_1(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.19/0.41  fof(c_0_32, plain, ![X15, X16, X17, X18]:(((X15=X17|~r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(k1_tarski(X17),k1_tarski(X18))))&(X16=X18|~r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(k1_tarski(X17),k1_tarski(X18)))))&(X15!=X17|X16!=X18|r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(k1_tarski(X17),k1_tarski(X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).
% 0.19/0.41  fof(c_0_33, plain, ![X19, X20, X21]:(k2_zfmisc_1(k1_tarski(X19),k2_tarski(X20,X21))=k2_tarski(k4_tarski(X19,X20),k4_tarski(X19,X21))&k2_zfmisc_1(k2_tarski(X19,X20),k1_tarski(X21))=k2_tarski(k4_tarski(X19,X21),k4_tarski(X20,X21))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.19/0.41  cnf(c_0_34, negated_conjecture, (k1_relat_1(esk10_0)!=k1_enumset1(esk8_0,esk8_0,esk8_0)|k2_relat_1(esk10_0)!=k1_enumset1(esk9_0,esk9_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_13]), c_0_13]), c_0_14]), c_0_14])).
% 0.19/0.41  cnf(c_0_35, negated_conjecture, (k1_enumset1(esk9_0,esk9_0,esk9_0)=k2_relat_1(esk10_0)|r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.41  cnf(c_0_36, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_37, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k1_tarski(X4),k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.41  cnf(c_0_38, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))|k1_enumset1(esk8_0,esk8_0,esk8_0)!=k1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.41  cnf(c_0_40, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_41, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k1_enumset1(X4,X4,X4),k1_enumset1(X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_13]), c_0_13]), c_0_14]), c_0_14])).
% 0.19/0.41  cnf(c_0_42, plain, (k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3))=k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_13]), c_0_14]), c_0_14]), c_0_14])).
% 0.19/0.41  cnf(c_0_43, plain, (r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (esk1_2(esk8_0,k1_relat_1(esk10_0))=esk8_0|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))|r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_25])])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (r2_hidden(esk8_0,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_40, c_0_27])).
% 0.19/0.41  cnf(c_0_46, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_47, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k1_enumset1(k4_tarski(X4,X2),k4_tarski(X4,X2),k4_tarski(X4,X2)))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.41  cnf(c_0_48, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_43])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_44]), c_0_45])]), c_0_39])).
% 0.19/0.41  cnf(c_0_50, plain, (X1=X3|X2!=k1_enumset1(X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_13]), c_0_14])).
% 0.19/0.41  cnf(c_0_51, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (X1=esk9_0|~r2_hidden(k4_tarski(X2,X1),esk10_0)), inference(spm,[status(thm)],[c_0_47, c_0_23])).
% 0.19/0.41  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0)|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.41  cnf(c_0_54, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.41  cnf(c_0_55, plain, (X1=X2|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(er,[status(thm)],[c_0_50])).
% 0.19/0.41  cnf(c_0_56, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_51])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (esk1_2(esk9_0,k2_relat_1(esk10_0))=esk9_0|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.41  cnf(c_0_58, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_enumset1(X2,X2,X2),k1_enumset1(X4,X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_13]), c_0_13]), c_0_14]), c_0_14])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (X1=k4_tarski(esk8_0,esk9_0)|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_55, c_0_23])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk2_3(esk10_0,k1_relat_1(esk10_0),esk8_0)),esk10_0)), inference(spm,[status(thm)],[c_0_56, c_0_45])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (k1_enumset1(esk9_0,esk9_0,esk9_0)=k2_relat_1(esk10_0)|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_57]), c_0_30])])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (k1_enumset1(esk8_0,esk8_0,esk8_0)=k1_relat_1(esk10_0)|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_29, c_0_45])).
% 0.19/0.41  cnf(c_0_63, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k1_enumset1(k4_tarski(X2,X4),k4_tarski(X2,X4),k4_tarski(X2,X4)))), inference(rw,[status(thm)],[c_0_58, c_0_42])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, (k4_tarski(esk8_0,esk2_3(esk10_0,k1_relat_1(esk10_0),esk8_0))=k4_tarski(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.41  cnf(c_0_65, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_61]), c_0_62])).
% 0.19/0.41  cnf(c_0_66, plain, (r2_hidden(esk6_2(X1,X2),X2)|r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_67, negated_conjecture, (X1=esk8_0|~r2_hidden(k4_tarski(X1,X2),esk10_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_23])).
% 0.19/0.41  cnf(c_0_68, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk2_3(esk10_0,k1_relat_1(esk10_0),esk1_2(esk8_0,k1_relat_1(esk10_0)))),esk10_0)), inference(spm,[status(thm)],[c_0_56, c_0_65])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, (r2_hidden(k4_tarski(esk7_2(X1,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk6_2(X1,k1_enumset1(esk9_0,esk9_0,esk9_0))),X1)|r2_hidden(esk6_2(X1,k1_enumset1(esk9_0,esk9_0,esk9_0)),k1_enumset1(esk9_0,esk9_0,esk9_0))|k1_enumset1(esk8_0,esk8_0,esk8_0)!=k1_relat_1(esk10_0)|k2_relat_1(X1)!=k2_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_34, c_0_66])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (esk1_2(esk8_0,k1_relat_1(esk10_0))=esk8_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.41  cnf(c_0_71, negated_conjecture, (r2_hidden(k4_tarski(esk7_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0))),esk10_0)|r2_hidden(esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),k1_enumset1(esk9_0,esk9_0,esk9_0))|k1_enumset1(esk8_0,esk8_0,esk8_0)!=k1_relat_1(esk10_0)), inference(er,[status(thm)],[c_0_69])).
% 0.19/0.41  cnf(c_0_72, negated_conjecture, (k1_enumset1(esk8_0,esk8_0,esk8_0)=k1_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_70]), c_0_45])])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (r2_hidden(k4_tarski(esk7_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0))),esk10_0)|r2_hidden(esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0)),k1_enumset1(esk9_0,esk9_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72])])).
% 0.19/0.41  cnf(c_0_74, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk6_2(X1,X2),X2)|~r2_hidden(k4_tarski(X3,esk6_2(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_75, negated_conjecture, (esk6_2(esk10_0,k1_enumset1(esk9_0,esk9_0,esk9_0))=esk9_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_73]), c_0_55])).
% 0.19/0.41  cnf(c_0_76, negated_conjecture, (k1_enumset1(esk9_0,esk9_0,esk9_0)!=k2_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_72])])).
% 0.19/0.41  cnf(c_0_77, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk9_0),esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_22])]), c_0_76])).
% 0.19/0.41  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_27, c_0_77]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 79
% 0.19/0.41  # Proof object clause steps            : 62
% 0.19/0.41  # Proof object formula steps           : 17
% 0.19/0.41  # Proof object conjectures             : 34
% 0.19/0.41  # Proof object clause conjectures      : 31
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 17
% 0.19/0.41  # Proof object initial formulas used   : 8
% 0.19/0.41  # Proof object generating inferences   : 25
% 0.19/0.41  # Proof object simplifying inferences  : 54
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 8
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 22
% 0.19/0.41  # Removed in clause preprocessing      : 2
% 0.19/0.41  # Initial clauses in saturation        : 20
% 0.19/0.41  # Processed clauses                    : 235
% 0.19/0.41  # ...of these trivial                  : 7
% 0.19/0.41  # ...subsumed                          : 29
% 0.19/0.41  # ...remaining for further processing  : 199
% 0.19/0.41  # Other redundant clauses eliminated   : 36
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 37
% 0.19/0.41  # Backward-rewritten                   : 43
% 0.19/0.41  # Generated clauses                    : 1940
% 0.19/0.41  # ...of the previous two non-trivial   : 1828
% 0.19/0.41  # Contextual simplify-reflections      : 6
% 0.19/0.41  # Paramodulations                      : 1902
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 37
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 90
% 0.19/0.41  #    Positive orientable unit clauses  : 39
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 2
% 0.19/0.41  #    Non-unit-clauses                  : 49
% 0.19/0.41  # Current number of unprocessed clauses: 1579
% 0.19/0.41  # ...number of literals in the above   : 6075
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 104
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 1747
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 806
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 68
% 0.19/0.41  # Unit Clause-clause subsumption calls : 232
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 43
% 0.19/0.41  # BW rewrite match successes           : 13
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 41620
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.069 s
% 0.19/0.42  # System time              : 0.005 s
% 0.19/0.42  # Total time               : 0.074 s
% 0.19/0.42  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
