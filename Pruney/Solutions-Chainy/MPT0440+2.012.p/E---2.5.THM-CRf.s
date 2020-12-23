%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:12 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 (6129 expanded)
%              Number of clauses        :   63 (2476 expanded)
%              Number of leaves         :    9 (1793 expanded)
%              Depth                    :   27
%              Number of atoms          :  186 (9598 expanded)
%              Number of equality atoms :   91 (7367 expanded)
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

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

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

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t129_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))
    <=> ( r2_hidden(X1,X3)
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

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
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( esk10_0 = k1_tarski(k4_tarski(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_16]),c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( esk10_0 = k2_enumset1(k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k2_relat_1(k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k2_zfmisc_1(k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)) = esk10_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_35,plain,
    ( X1 = k4_tarski(X2,X3)
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk9_0,k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_40,plain,(
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

cnf(c_0_41,negated_conjecture,
    ( X1 = k4_tarski(esk8_0,esk9_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk9_0),esk9_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( X2 = k2_enumset1(X1,X1,X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_44,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk9_0),esk9_0) = k4_tarski(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( k1_relat_1(esk10_0) != k1_tarski(esk8_0)
    | k2_relat_1(esk10_0) != k1_tarski(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,plain,
    ( X1 = k2_enumset1(X2,X2,X2,X2)
    | r2_hidden(esk1_2(X2,X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk9_0),esk10_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_46])).

fof(c_0_51,plain,(
    ! [X18,X19,X20,X21] :
      ( ( r2_hidden(X18,X20)
        | ~ r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,k1_tarski(X21))) )
      & ( X19 = X21
        | ~ r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,k1_tarski(X21))) )
      & ( ~ r2_hidden(X18,X20)
        | X19 != X21
        | r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,k1_tarski(X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(esk10_0) != k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)
    | k2_relat_1(esk10_0) != k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_18]),c_0_18])).

cnf(c_0_53,negated_conjecture,
    ( k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0) = k2_relat_1(esk10_0)
    | r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk8_0,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))
    | k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0) != k1_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0) = k1_relat_1(esk10_0)
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_54])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))
    | r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( X1 = esk9_0
    | ~ r2_hidden(k4_tarski(X2,X1),esk10_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_34])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0)
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( esk1_2(esk9_0,k2_relat_1(esk10_0)) = esk9_0
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_63,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_64,negated_conjecture,
    ( k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0) = k2_relat_1(esk10_0)
    | r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_62]),c_0_37])])).

cnf(c_0_65,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_64]),c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk2_3(esk10_0,k1_relat_1(esk10_0),esk1_2(esk8_0,k1_relat_1(esk10_0)))),esk10_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k1_tarski(X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_69,negated_conjecture,
    ( esk2_3(esk10_0,k1_relat_1(esk10_0),esk1_2(esk8_0,k1_relat_1(esk10_0))) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_67])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k2_enumset1(X4,X4,X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk9_0),esk10_0) ),
    inference(rw,[status(thm)],[c_0_67,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(X1,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))
    | ~ r2_hidden(k4_tarski(X1,X2),esk10_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_34])).

cnf(c_0_73,negated_conjecture,
    ( k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk9_0) = k4_tarski(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_50])])).

cnf(c_0_75,negated_conjecture,
    ( esk1_2(esk8_0,k1_relat_1(esk10_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0) = k1_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_75]),c_0_54])])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_76])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_77])).

cnf(c_0_79,negated_conjecture,
    ( esk1_2(esk9_0,k2_relat_1(esk10_0)) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_78])).

cnf(c_0_80,negated_conjecture,
    ( k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0) != k2_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_76])])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_79]),c_0_37])]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.51  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.51  # and selection function SelectNegativeLiterals.
% 0.19/0.51  #
% 0.19/0.51  # Preprocessing time       : 0.029 s
% 0.19/0.51  # Presaturation interreduction done
% 0.19/0.51  
% 0.19/0.51  # Proof found!
% 0.19/0.51  # SZS status Theorem
% 0.19/0.51  # SZS output start CNFRefutation
% 0.19/0.51  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.51  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.51  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.51  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.51  fof(t23_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relat_1)).
% 0.19/0.51  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.51  fof(t35_zfmisc_1, axiom, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 0.19/0.51  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.19/0.51  fof(t129_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))<=>(r2_hidden(X1,X3)&X2=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 0.19/0.51  fof(c_0_9, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.51  fof(c_0_10, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.51  fof(c_0_11, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.51  fof(c_0_12, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.51  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2))))), inference(assume_negation,[status(cth)],[t23_relat_1])).
% 0.19/0.51  fof(c_0_14, plain, ![X35, X36, X37, X39, X40, X41, X42, X44]:(((~r2_hidden(X37,X36)|r2_hidden(k4_tarski(esk5_3(X35,X36,X37),X37),X35)|X36!=k2_relat_1(X35))&(~r2_hidden(k4_tarski(X40,X39),X35)|r2_hidden(X39,X36)|X36!=k2_relat_1(X35)))&((~r2_hidden(esk6_2(X41,X42),X42)|~r2_hidden(k4_tarski(X44,esk6_2(X41,X42)),X41)|X42=k2_relat_1(X41))&(r2_hidden(esk6_2(X41,X42),X42)|r2_hidden(k4_tarski(esk7_2(X41,X42),esk6_2(X41,X42)),X41)|X42=k2_relat_1(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.51  cnf(c_0_15, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.51  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.51  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.51  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.51  fof(c_0_19, plain, ![X22, X23]:k2_zfmisc_1(k1_tarski(X22),k1_tarski(X23))=k1_tarski(k4_tarski(X22,X23)), inference(variable_rename,[status(thm)],[t35_zfmisc_1])).
% 0.19/0.51  fof(c_0_20, negated_conjecture, (v1_relat_1(esk10_0)&(esk10_0=k1_tarski(k4_tarski(esk8_0,esk9_0))&(k1_relat_1(esk10_0)!=k1_tarski(esk8_0)|k2_relat_1(esk10_0)!=k1_tarski(esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.19/0.51  cnf(c_0_21, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.51  cnf(c_0_22, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.51  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.19/0.51  cnf(c_0_24, plain, (k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.51  cnf(c_0_25, negated_conjecture, (esk10_0=k1_tarski(k4_tarski(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.51  cnf(c_0_26, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_16]), c_0_17]), c_0_18])).
% 0.19/0.51  cnf(c_0_27, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_22])).
% 0.19/0.51  cnf(c_0_28, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).
% 0.19/0.51  cnf(c_0_29, plain, (k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_16]), c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_18])).
% 0.19/0.51  cnf(c_0_30, negated_conjecture, (esk10_0=k2_enumset1(k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_16]), c_0_17]), c_0_18])).
% 0.19/0.51  cnf(c_0_31, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_26])).
% 0.19/0.51  cnf(c_0_32, plain, (r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.51  cnf(c_0_33, plain, (r2_hidden(X1,k2_relat_1(k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.19/0.51  cnf(c_0_34, negated_conjecture, (k2_zfmisc_1(k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))=esk10_0), inference(rw,[status(thm)],[c_0_30, c_0_29])).
% 0.19/0.51  cnf(c_0_35, plain, (X1=k4_tarski(X2,X3)|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.19/0.51  cnf(c_0_36, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.51  cnf(c_0_37, negated_conjecture, (r2_hidden(esk9_0,k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.51  cnf(c_0_38, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.51  cnf(c_0_39, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.51  fof(c_0_40, plain, ![X24, X25, X26, X28, X29, X30, X31, X33]:(((~r2_hidden(X26,X25)|r2_hidden(k4_tarski(X26,esk2_3(X24,X25,X26)),X24)|X25!=k1_relat_1(X24))&(~r2_hidden(k4_tarski(X28,X29),X24)|r2_hidden(X28,X25)|X25!=k1_relat_1(X24)))&((~r2_hidden(esk3_2(X30,X31),X31)|~r2_hidden(k4_tarski(esk3_2(X30,X31),X33),X30)|X31=k1_relat_1(X30))&(r2_hidden(esk3_2(X30,X31),X31)|r2_hidden(k4_tarski(esk3_2(X30,X31),esk4_2(X30,X31)),X30)|X31=k1_relat_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.19/0.51  cnf(c_0_41, negated_conjecture, (X1=k4_tarski(esk8_0,esk9_0)|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.19/0.51  cnf(c_0_42, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk9_0),esk9_0),esk10_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.51  cnf(c_0_43, plain, (X2=k2_enumset1(X1,X1,X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_16]), c_0_17]), c_0_18])).
% 0.19/0.51  cnf(c_0_44, plain, (esk1_2(X1,X2)=X1|X2=k2_enumset1(X1,X1,X1,X1)|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_16]), c_0_17]), c_0_18])).
% 0.19/0.51  cnf(c_0_45, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.51  cnf(c_0_46, negated_conjecture, (k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk9_0),esk9_0)=k4_tarski(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.51  cnf(c_0_47, negated_conjecture, (k1_relat_1(esk10_0)!=k1_tarski(esk8_0)|k2_relat_1(esk10_0)!=k1_tarski(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.51  cnf(c_0_48, plain, (X1=k2_enumset1(X2,X2,X2,X2)|r2_hidden(esk1_2(X2,X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.51  cnf(c_0_49, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_45])).
% 0.19/0.51  cnf(c_0_50, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk9_0),esk10_0)), inference(rw,[status(thm)],[c_0_42, c_0_46])).
% 0.19/0.51  fof(c_0_51, plain, ![X18, X19, X20, X21]:(((r2_hidden(X18,X20)|~r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,k1_tarski(X21))))&(X19=X21|~r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,k1_tarski(X21)))))&(~r2_hidden(X18,X20)|X19!=X21|r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,k1_tarski(X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t129_zfmisc_1])])])).
% 0.19/0.51  cnf(c_0_52, negated_conjecture, (k1_relat_1(esk10_0)!=k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)|k2_relat_1(esk10_0)!=k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_18]), c_0_18])).
% 0.19/0.51  cnf(c_0_53, negated_conjecture, (k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)=k2_relat_1(esk10_0)|r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_48, c_0_37])).
% 0.19/0.51  cnf(c_0_54, negated_conjecture, (r2_hidden(esk8_0,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.51  cnf(c_0_55, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.51  cnf(c_0_56, negated_conjecture, (r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))|k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)!=k1_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.51  cnf(c_0_57, negated_conjecture, (k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)=k1_relat_1(esk10_0)|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_48, c_0_54])).
% 0.19/0.51  cnf(c_0_58, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_16]), c_0_17]), c_0_18])).
% 0.19/0.51  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))|r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.51  cnf(c_0_60, negated_conjecture, (X1=esk9_0|~r2_hidden(k4_tarski(X2,X1),esk10_0)), inference(spm,[status(thm)],[c_0_58, c_0_34])).
% 0.19/0.51  cnf(c_0_61, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0)|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_36, c_0_59])).
% 0.19/0.51  cnf(c_0_62, negated_conjecture, (esk1_2(esk9_0,k2_relat_1(esk10_0))=esk9_0|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.51  cnf(c_0_63, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.51  cnf(c_0_64, negated_conjecture, (k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)=k2_relat_1(esk10_0)|r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_62]), c_0_37])])).
% 0.19/0.51  cnf(c_0_65, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_63])).
% 0.19/0.51  cnf(c_0_66, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k1_relat_1(esk10_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_64]), c_0_57])).
% 0.19/0.51  cnf(c_0_67, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk2_3(esk10_0,k1_relat_1(esk10_0),esk1_2(esk8_0,k1_relat_1(esk10_0)))),esk10_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.51  cnf(c_0_68, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k1_tarski(X4)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.51  cnf(c_0_69, negated_conjecture, (esk2_3(esk10_0,k1_relat_1(esk10_0),esk1_2(esk8_0,k1_relat_1(esk10_0)))=esk9_0), inference(spm,[status(thm)],[c_0_60, c_0_67])).
% 0.19/0.51  cnf(c_0_70, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,k2_enumset1(X4,X4,X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_16]), c_0_17]), c_0_18])).
% 0.19/0.51  cnf(c_0_71, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk9_0),esk10_0)), inference(rw,[status(thm)],[c_0_67, c_0_69])).
% 0.19/0.51  cnf(c_0_72, negated_conjecture, (r2_hidden(X1,k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))|~r2_hidden(k4_tarski(X1,X2),esk10_0)), inference(spm,[status(thm)],[c_0_70, c_0_34])).
% 0.19/0.51  cnf(c_0_73, negated_conjecture, (k4_tarski(esk1_2(esk8_0,k1_relat_1(esk10_0)),esk9_0)=k4_tarski(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_41, c_0_71])).
% 0.19/0.51  cnf(c_0_74, negated_conjecture, (r2_hidden(esk1_2(esk8_0,k1_relat_1(esk10_0)),k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_50])])).
% 0.19/0.51  cnf(c_0_75, negated_conjecture, (esk1_2(esk8_0,k1_relat_1(esk10_0))=esk8_0), inference(spm,[status(thm)],[c_0_31, c_0_74])).
% 0.19/0.51  cnf(c_0_76, negated_conjecture, (k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)=k1_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_75]), c_0_54])])).
% 0.19/0.51  cnf(c_0_77, negated_conjecture, (r2_hidden(esk1_2(esk9_0,k2_relat_1(esk10_0)),k2_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_76])])).
% 0.19/0.51  cnf(c_0_78, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk10_0,k2_relat_1(esk10_0),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk1_2(esk9_0,k2_relat_1(esk10_0))),esk10_0)), inference(spm,[status(thm)],[c_0_36, c_0_77])).
% 0.19/0.51  cnf(c_0_79, negated_conjecture, (esk1_2(esk9_0,k2_relat_1(esk10_0))=esk9_0), inference(spm,[status(thm)],[c_0_60, c_0_78])).
% 0.19/0.51  cnf(c_0_80, negated_conjecture, (k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)!=k2_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_76])])).
% 0.19/0.51  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_79]), c_0_37])]), c_0_80]), ['proof']).
% 0.19/0.51  # SZS output end CNFRefutation
% 0.19/0.51  # Proof object total steps             : 82
% 0.19/0.51  # Proof object clause steps            : 63
% 0.19/0.51  # Proof object formula steps           : 19
% 0.19/0.51  # Proof object conjectures             : 36
% 0.19/0.51  # Proof object clause conjectures      : 33
% 0.19/0.51  # Proof object formula conjectures     : 3
% 0.19/0.51  # Proof object initial clauses used    : 16
% 0.19/0.51  # Proof object initial formulas used   : 9
% 0.19/0.51  # Proof object generating inferences   : 27
% 0.19/0.51  # Proof object simplifying inferences  : 61
% 0.19/0.51  # Training examples: 0 positive, 0 negative
% 0.19/0.51  # Parsed axioms                        : 9
% 0.19/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.51  # Initial clauses                      : 22
% 0.19/0.51  # Removed in clause preprocessing      : 3
% 0.19/0.51  # Initial clauses in saturation        : 19
% 0.19/0.51  # Processed clauses                    : 354
% 0.19/0.51  # ...of these trivial                  : 5
% 0.19/0.51  # ...subsumed                          : 53
% 0.19/0.51  # ...remaining for further processing  : 296
% 0.19/0.51  # Other redundant clauses eliminated   : 68
% 0.19/0.51  # Clauses deleted for lack of memory   : 0
% 0.19/0.51  # Backward-subsumed                    : 79
% 0.19/0.51  # Backward-rewritten                   : 63
% 0.19/0.51  # Generated clauses                    : 6489
% 0.19/0.51  # ...of the previous two non-trivial   : 6176
% 0.19/0.51  # Contextual simplify-reflections      : 5
% 0.19/0.51  # Paramodulations                      : 6421
% 0.19/0.51  # Factorizations                       : 0
% 0.19/0.51  # Equation resolutions                 : 68
% 0.19/0.51  # Propositional unsat checks           : 0
% 0.19/0.51  #    Propositional check models        : 0
% 0.19/0.51  #    Propositional check unsatisfiable : 0
% 0.19/0.51  #    Propositional clauses             : 0
% 0.19/0.51  #    Propositional clauses after purity: 0
% 0.19/0.51  #    Propositional unsat core size     : 0
% 0.19/0.51  #    Propositional preprocessing time  : 0.000
% 0.19/0.51  #    Propositional encoding time       : 0.000
% 0.19/0.51  #    Propositional solver time         : 0.000
% 0.19/0.51  #    Success case prop preproc time    : 0.000
% 0.19/0.51  #    Success case prop encoding time   : 0.000
% 0.19/0.51  #    Success case prop solver time     : 0.000
% 0.19/0.51  # Current number of processed clauses  : 127
% 0.19/0.51  #    Positive orientable unit clauses  : 40
% 0.19/0.51  #    Positive unorientable unit clauses: 0
% 0.19/0.51  #    Negative unit clauses             : 1
% 0.19/0.51  #    Non-unit-clauses                  : 86
% 0.19/0.51  # Current number of unprocessed clauses: 5730
% 0.19/0.51  # ...number of literals in the above   : 30070
% 0.19/0.51  # Current number of archived formulas  : 0
% 0.19/0.51  # Current number of archived clauses   : 165
% 0.19/0.51  # Clause-clause subsumption calls (NU) : 4675
% 0.19/0.51  # Rec. Clause-clause subsumption calls : 1271
% 0.19/0.51  # Non-unit clause-clause subsumptions  : 135
% 0.19/0.51  # Unit Clause-clause subsumption calls : 605
% 0.19/0.51  # Rewrite failures with RHS unbound    : 0
% 0.19/0.51  # BW rewrite match attempts            : 57
% 0.19/0.51  # BW rewrite match successes           : 13
% 0.19/0.51  # Condensation attempts                : 0
% 0.19/0.51  # Condensation successes               : 0
% 0.19/0.51  # Termbank termtop insertions          : 162844
% 0.19/0.51  
% 0.19/0.51  # -------------------------------------------------
% 0.19/0.51  # User time                : 0.162 s
% 0.19/0.51  # System time              : 0.010 s
% 0.19/0.51  # Total time               : 0.172 s
% 0.19/0.51  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
