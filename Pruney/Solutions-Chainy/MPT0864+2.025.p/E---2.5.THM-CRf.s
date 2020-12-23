%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:21 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   74 (1049 expanded)
%              Number of clauses        :   55 ( 484 expanded)
%              Number of leaves         :    9 ( 251 expanded)
%              Depth                    :   21
%              Number of atoms          :  177 (2763 expanded)
%              Number of equality atoms :  140 (2200 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

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

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_10,plain,(
    ! [X29,X30] :
      ( k1_mcart_1(k4_tarski(X29,X30)) = X29
      & k2_mcart_1(k4_tarski(X29,X30)) = X30 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_11,negated_conjecture,
    ( esk4_0 = k4_tarski(esk5_0,esk6_0)
    & ( esk4_0 = k1_mcart_1(esk4_0)
      | esk4_0 = k2_mcart_1(esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
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

fof(c_0_13,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_16,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( esk4_0 = k4_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( esk5_0 = k1_mcart_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_23,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X12
        | X15 = X13
        | X14 != k2_tarski(X12,X13) )
      & ( X16 != X12
        | r2_hidden(X16,X14)
        | X14 != k2_tarski(X12,X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k2_tarski(X12,X13) )
      & ( esk2_3(X17,X18,X19) != X17
        | ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k2_tarski(X17,X18) )
      & ( esk2_3(X17,X18,X19) != X18
        | ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k2_tarski(X17,X18) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X19)
        | esk2_3(X17,X18,X19) = X17
        | esk2_3(X17,X18,X19) = X18
        | X19 = k2_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_24,plain,(
    ! [X31,X33,X34] :
      ( ( r2_hidden(esk3_1(X31),X31)
        | X31 = k1_xboole_0 )
      & ( ~ r2_hidden(X33,X31)
        | esk3_1(X31) != k4_tarski(X33,X34)
        | X31 = k1_xboole_0 )
      & ( ~ r2_hidden(X34,X31)
        | esk3_1(X31) != k4_tarski(X33,X34)
        | X31 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_25,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_26,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk4_0),esk6_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_28,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k4_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( esk6_0 = k2_mcart_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_20]),c_0_21])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(X2,esk3_1(X1)) != esk3_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( esk3_1(k2_enumset1(X1,X1,X1,X1)) = X1
    | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk4_0),k2_mcart_1(esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( esk4_0 = k1_mcart_1(esk4_0)
    | esk4_0 = k2_mcart_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk3_1(X2) != k4_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_41,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | k4_tarski(X2,X1) != X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk4_0),esk4_0) = esk4_0
    | k1_mcart_1(esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_20]),c_0_21])).

cnf(c_0_44,plain,
    ( esk3_1(k2_enumset1(X1,X1,X1,X2)) = X2
    | esk3_1(k2_enumset1(X1,X1,X1,X2)) = X1
    | k2_enumset1(X1,X1,X1,X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_30])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(esk3_1(X1),X2) != esk3_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | k1_mcart_1(esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).

cnf(c_0_49,plain,
    ( esk3_1(k2_enumset1(X1,X1,X1,X2)) = X2
    | k2_enumset1(X1,X1,X1,X2) = k1_xboole_0
    | k4_tarski(X3,X1) != X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_44])).

cnf(c_0_50,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | k4_tarski(X1,X2) != X1 ),
    inference(spm,[status(thm)],[c_0_45,c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | k4_tarski(esk4_0,k2_mcart_1(esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_46])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_20]),c_0_21])).

cnf(c_0_53,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k1_xboole_0
    | esk3_1(k2_enumset1(X1,X1,X1,X2)) != k4_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( esk3_1(k2_enumset1(esk4_0,esk4_0,esk4_0,X1)) = X1
    | k2_enumset1(esk4_0,esk4_0,esk4_0,X1) = k1_xboole_0
    | k1_mcart_1(esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).

cnf(c_0_57,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,k4_tarski(esk4_0,X1)) = k1_xboole_0
    | k1_mcart_1(esk4_0) = esk4_0 ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_58,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( k1_mcart_1(esk4_0) = esk4_0
    | r2_hidden(k4_tarski(esk4_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( k4_tarski(esk4_0,X1) = esk4_0
    | k1_mcart_1(esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( k1_mcart_1(esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_60])).

cnf(c_0_62,plain,
    ( esk3_1(k2_enumset1(X1,X1,X1,X2)) = X2
    | k2_enumset1(X1,X1,X1,X2) = k1_xboole_0
    | k4_tarski(X1,X3) != X1 ),
    inference(spm,[status(thm)],[c_0_45,c_0_44])).

cnf(c_0_63,negated_conjecture,
    ( k4_tarski(esk4_0,k2_mcart_1(esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( esk3_1(k2_enumset1(esk4_0,esk4_0,esk4_0,X1)) = X1
    | k2_enumset1(esk4_0,esk4_0,esk4_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_65,plain,(
    ! [X27,X28] : k2_xboole_0(k1_tarski(X27),X28) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_66,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,k4_tarski(esk4_0,X1)) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_64])])).

cnf(c_0_67,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_66])).

cnf(c_0_69,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_70,negated_conjecture,
    ( k4_tarski(esk4_0,X1) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_55])).

cnf(c_0_72,negated_conjecture,
    ( k2_mcart_1(esk4_0) = X1 ),
    inference(spm,[status(thm)],[c_0_26,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:17:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.13/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.13/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.13/0.37  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.37  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.13/0.37  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.13/0.37  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.13/0.37  fof(c_0_9, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.13/0.37  fof(c_0_10, plain, ![X29, X30]:(k1_mcart_1(k4_tarski(X29,X30))=X29&k2_mcart_1(k4_tarski(X29,X30))=X30), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.13/0.37  fof(c_0_11, negated_conjecture, (esk4_0=k4_tarski(esk5_0,esk6_0)&(esk4_0=k1_mcart_1(esk4_0)|esk4_0=k2_mcart_1(esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.13/0.37  fof(c_0_12, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.37  fof(c_0_13, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.37  fof(c_0_14, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.37  fof(c_0_15, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.37  cnf(c_0_16, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (esk4_0=k4_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_18, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (esk5_0=k1_mcart_1(esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.37  fof(c_0_23, plain, ![X12, X13, X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X15,X14)|(X15=X12|X15=X13)|X14!=k2_tarski(X12,X13))&((X16!=X12|r2_hidden(X16,X14)|X14!=k2_tarski(X12,X13))&(X16!=X13|r2_hidden(X16,X14)|X14!=k2_tarski(X12,X13))))&(((esk2_3(X17,X18,X19)!=X17|~r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k2_tarski(X17,X18))&(esk2_3(X17,X18,X19)!=X18|~r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k2_tarski(X17,X18)))&(r2_hidden(esk2_3(X17,X18,X19),X19)|(esk2_3(X17,X18,X19)=X17|esk2_3(X17,X18,X19)=X18)|X19=k2_tarski(X17,X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.13/0.37  fof(c_0_24, plain, ![X31, X33, X34]:((r2_hidden(esk3_1(X31),X31)|X31=k1_xboole_0)&((~r2_hidden(X33,X31)|esk3_1(X31)!=k4_tarski(X33,X34)|X31=k1_xboole_0)&(~r2_hidden(X34,X31)|esk3_1(X31)!=k4_tarski(X33,X34)|X31=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.13/0.37  cnf(c_0_25, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])).
% 0.13/0.37  cnf(c_0_26, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (k4_tarski(k1_mcart_1(esk4_0),esk6_0)=esk4_0), inference(rw,[status(thm)],[c_0_17, c_0_22])).
% 0.13/0.37  cnf(c_0_28, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  cnf(c_0_29, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k4_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.37  cnf(c_0_30, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.37  cnf(c_0_31, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (esk6_0=k2_mcart_1(esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.37  cnf(c_0_33, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_20]), c_0_21])).
% 0.13/0.37  cnf(c_0_34, plain, (X1=k1_xboole_0|k4_tarski(X2,esk3_1(X1))!=esk3_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.37  cnf(c_0_35, plain, (esk3_1(k2_enumset1(X1,X1,X1,X1))=X1|k2_enumset1(X1,X1,X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (k4_tarski(k1_mcart_1(esk4_0),k2_mcart_1(esk4_0))=esk4_0), inference(rw,[status(thm)],[c_0_27, c_0_32])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (esk4_0=k1_mcart_1(esk4_0)|esk4_0=k2_mcart_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_38, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  cnf(c_0_39, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_33])).
% 0.13/0.37  cnf(c_0_40, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk3_1(X2)!=k4_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.37  cnf(c_0_41, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|k4_tarski(X2,X1)!=X1), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (k4_tarski(k1_mcart_1(esk4_0),esk4_0)=esk4_0|k1_mcart_1(esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.37  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_20]), c_0_21])).
% 0.13/0.37  cnf(c_0_44, plain, (esk3_1(k2_enumset1(X1,X1,X1,X2))=X2|esk3_1(k2_enumset1(X1,X1,X1,X2))=X1|k2_enumset1(X1,X1,X1,X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_30])).
% 0.13/0.37  cnf(c_0_45, plain, (X1=k1_xboole_0|k4_tarski(esk3_1(X1),X2)!=esk3_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_30])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0|k1_mcart_1(esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.37  cnf(c_0_47, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  cnf(c_0_48, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).
% 0.13/0.37  cnf(c_0_49, plain, (esk3_1(k2_enumset1(X1,X1,X1,X2))=X2|k2_enumset1(X1,X1,X1,X2)=k1_xboole_0|k4_tarski(X3,X1)!=X1), inference(spm,[status(thm)],[c_0_34, c_0_44])).
% 0.13/0.37  cnf(c_0_50, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|k4_tarski(X1,X2)!=X1), inference(spm,[status(thm)],[c_0_45, c_0_35])).
% 0.13/0.37  cnf(c_0_51, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0|k4_tarski(esk4_0,k2_mcart_1(esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_36, c_0_46])).
% 0.13/0.37  cnf(c_0_52, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_20]), c_0_21])).
% 0.13/0.37  cnf(c_0_53, plain, (k2_enumset1(X1,X1,X1,X2)=k1_xboole_0|esk3_1(k2_enumset1(X1,X1,X1,X2))!=k4_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_40, c_0_48])).
% 0.13/0.37  cnf(c_0_54, negated_conjecture, (esk3_1(k2_enumset1(esk4_0,esk4_0,esk4_0,X1))=X1|k2_enumset1(esk4_0,esk4_0,esk4_0,X1)=k1_xboole_0|k1_mcart_1(esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_49, c_0_42])).
% 0.13/0.37  cnf(c_0_55, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.37  cnf(c_0_56, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).
% 0.13/0.37  cnf(c_0_57, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,k4_tarski(esk4_0,X1))=k1_xboole_0|k1_mcart_1(esk4_0)=esk4_0), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54])])).
% 0.13/0.37  cnf(c_0_58, negated_conjecture, (X1=esk4_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_55])).
% 0.13/0.37  cnf(c_0_59, negated_conjecture, (k1_mcart_1(esk4_0)=esk4_0|r2_hidden(k4_tarski(esk4_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.37  cnf(c_0_60, negated_conjecture, (k4_tarski(esk4_0,X1)=esk4_0|k1_mcart_1(esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.13/0.37  cnf(c_0_61, negated_conjecture, (k1_mcart_1(esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_16, c_0_60])).
% 0.13/0.37  cnf(c_0_62, plain, (esk3_1(k2_enumset1(X1,X1,X1,X2))=X2|k2_enumset1(X1,X1,X1,X2)=k1_xboole_0|k4_tarski(X1,X3)!=X1), inference(spm,[status(thm)],[c_0_45, c_0_44])).
% 0.13/0.37  cnf(c_0_63, negated_conjecture, (k4_tarski(esk4_0,k2_mcart_1(esk4_0))=esk4_0), inference(rw,[status(thm)],[c_0_36, c_0_61])).
% 0.13/0.37  cnf(c_0_64, negated_conjecture, (esk3_1(k2_enumset1(esk4_0,esk4_0,esk4_0,X1))=X1|k2_enumset1(esk4_0,esk4_0,esk4_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.13/0.37  fof(c_0_65, plain, ![X27, X28]:k2_xboole_0(k1_tarski(X27),X28)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.13/0.37  cnf(c_0_66, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,k4_tarski(esk4_0,X1))=k1_xboole_0), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_64])])).
% 0.13/0.37  cnf(c_0_67, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.37  cnf(c_0_68, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_66])).
% 0.13/0.37  cnf(c_0_69, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_19]), c_0_20]), c_0_21])).
% 0.13/0.37  cnf(c_0_70, negated_conjecture, (k4_tarski(esk4_0,X1)=esk4_0), inference(spm,[status(thm)],[c_0_58, c_0_68])).
% 0.13/0.37  cnf(c_0_71, negated_conjecture, (k2_xboole_0(k1_xboole_0,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_55])).
% 0.13/0.37  cnf(c_0_72, negated_conjecture, (k2_mcart_1(esk4_0)=X1), inference(spm,[status(thm)],[c_0_26, c_0_70])).
% 0.13/0.37  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_72]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 74
% 0.13/0.37  # Proof object clause steps            : 55
% 0.13/0.37  # Proof object formula steps           : 19
% 0.13/0.37  # Proof object conjectures             : 27
% 0.13/0.37  # Proof object clause conjectures      : 24
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 15
% 0.13/0.37  # Proof object initial formulas used   : 9
% 0.13/0.37  # Proof object generating inferences   : 28
% 0.13/0.37  # Proof object simplifying inferences  : 24
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 9
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 21
% 0.13/0.37  # Removed in clause preprocessing      : 3
% 0.13/0.37  # Initial clauses in saturation        : 18
% 0.13/0.37  # Processed clauses                    : 119
% 0.13/0.37  # ...of these trivial                  : 4
% 0.13/0.37  # ...subsumed                          : 23
% 0.13/0.37  # ...remaining for further processing  : 92
% 0.13/0.37  # Other redundant clauses eliminated   : 38
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 4
% 0.13/0.37  # Backward-rewritten                   : 23
% 0.13/0.37  # Generated clauses                    : 354
% 0.13/0.37  # ...of the previous two non-trivial   : 260
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 306
% 0.13/0.37  # Factorizations                       : 12
% 0.13/0.37  # Equation resolutions                 : 38
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 42
% 0.13/0.37  #    Positive orientable unit clauses  : 9
% 0.13/0.37  #    Positive unorientable unit clauses: 1
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 30
% 0.13/0.37  # Current number of unprocessed clauses: 119
% 0.13/0.37  # ...number of literals in the above   : 420
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 48
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 146
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 135
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 21
% 0.13/0.37  # Unit Clause-clause subsumption calls : 33
% 0.13/0.37  # Rewrite failures with RHS unbound    : 5
% 0.13/0.37  # BW rewrite match attempts            : 58
% 0.13/0.37  # BW rewrite match successes           : 48
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 4604
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.033 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.037 s
% 0.13/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
