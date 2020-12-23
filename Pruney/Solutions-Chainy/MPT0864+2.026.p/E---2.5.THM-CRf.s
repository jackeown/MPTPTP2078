%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:21 EST 2020

% Result     : Theorem 15.00s
% Output     : CNFRefutation 15.00s
% Verified   : 
% Statistics : Number of formulae       :   78 (1687 expanded)
%              Number of clauses        :   57 ( 783 expanded)
%              Number of leaves         :   10 ( 426 expanded)
%              Depth                    :   21
%              Number of atoms          :  205 (4739 expanded)
%              Number of equality atoms :  130 (3274 expanded)
%              Maximal formula depth    :   23 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(c_0_10,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X7
        | X8 != k1_tarski(X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k1_tarski(X7) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | esk1_2(X11,X12) != X11
        | X12 = k1_tarski(X11) )
      & ( r2_hidden(esk1_2(X11,X12),X12)
        | esk1_2(X11,X12) = X11
        | X12 = k1_tarski(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X20,X21,X22,X23,X26,X27,X28,X29,X30,X31,X33,X34] :
      ( ( r2_hidden(esk2_4(X20,X21,X22,X23),X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k2_zfmisc_1(X20,X21) )
      & ( r2_hidden(esk3_4(X20,X21,X22,X23),X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k2_zfmisc_1(X20,X21) )
      & ( X23 = k4_tarski(esk2_4(X20,X21,X22,X23),esk3_4(X20,X21,X22,X23))
        | ~ r2_hidden(X23,X22)
        | X22 != k2_zfmisc_1(X20,X21) )
      & ( ~ r2_hidden(X27,X20)
        | ~ r2_hidden(X28,X21)
        | X26 != k4_tarski(X27,X28)
        | r2_hidden(X26,X22)
        | X22 != k2_zfmisc_1(X20,X21) )
      & ( ~ r2_hidden(esk4_3(X29,X30,X31),X31)
        | ~ r2_hidden(X33,X29)
        | ~ r2_hidden(X34,X30)
        | esk4_3(X29,X30,X31) != k4_tarski(X33,X34)
        | X31 = k2_zfmisc_1(X29,X30) )
      & ( r2_hidden(esk5_3(X29,X30,X31),X29)
        | r2_hidden(esk4_3(X29,X30,X31),X31)
        | X31 = k2_zfmisc_1(X29,X30) )
      & ( r2_hidden(esk6_3(X29,X30,X31),X30)
        | r2_hidden(esk4_3(X29,X30,X31),X31)
        | X31 = k2_zfmisc_1(X29,X30) )
      & ( esk4_3(X29,X30,X31) = k4_tarski(esk5_3(X29,X30,X31),esk6_3(X29,X30,X31))
        | r2_hidden(esk4_3(X29,X30,X31),X31)
        | X31 = k2_zfmisc_1(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X3))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_25,negated_conjecture,
    ( esk8_0 = k4_tarski(esk9_0,esk10_0)
    & ( esk8_0 = k1_mcart_1(esk8_0)
      | esk8_0 = k2_mcart_1(esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_26,plain,(
    ! [X37,X38] :
      ( ( k2_zfmisc_1(X37,X38) != k1_xboole_0
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0 )
      & ( X37 != k1_xboole_0
        | k2_zfmisc_1(X37,X38) = k1_xboole_0 )
      & ( X38 != k1_xboole_0
        | k2_zfmisc_1(X37,X38) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_27,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( esk8_0 = k4_tarski(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X43,X45,X46] :
      ( ( r2_hidden(esk7_1(X43),X43)
        | X43 = k1_xboole_0 )
      & ( ~ r2_hidden(X45,X43)
        | esk7_1(X43) != k4_tarski(X45,X46)
        | X43 = k1_xboole_0 )
      & ( ~ r2_hidden(X46,X43)
        | esk7_1(X43) != k4_tarski(X45,X46)
        | X43 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk8_0,k2_zfmisc_1(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0),k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(esk7_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X41,X42] :
      ( k1_mcart_1(k4_tarski(X41,X42)) = X41
      & k2_mcart_1(k4_tarski(X41,X42)) = X42 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk7_1(k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0)),k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0))
    | r2_hidden(esk8_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_39,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk7_1(X2) != k4_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( esk7_1(k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0)) = esk10_0
    | r2_hidden(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( esk8_0 = k1_mcart_1(esk8_0)
    | esk8_0 = k2_mcart_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( k1_mcart_1(esk8_0) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_29])).

cnf(c_0_45,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0) = k1_xboole_0
    | r2_hidden(esk8_0,k1_xboole_0)
    | k4_tarski(X1,X2) != esk10_0
    | ~ r2_hidden(X2,k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k2_mcart_1(esk8_0) = esk8_0
    | esk9_0 = esk8_0 ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k2_mcart_1(esk8_0) = esk10_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_29])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk7_1(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))
    | r2_hidden(esk8_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0) = k1_xboole_0
    | r2_hidden(esk8_0,k1_xboole_0)
    | esk10_0 != esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_29]),c_0_22])])).

cnf(c_0_52,negated_conjecture,
    ( esk9_0 = esk8_0
    | esk10_0 = esk8_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk7_1(X2) != k4_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_54,negated_conjecture,
    ( esk7_1(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)) = esk9_0
    | r2_hidden(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0) = k1_xboole_0
    | esk9_0 = esk8_0
    | r2_hidden(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( X1 = k4_tarski(esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,negated_conjecture,
    ( k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0) = k1_xboole_0
    | r2_hidden(esk8_0,k1_xboole_0)
    | k4_tarski(X1,X2) != esk9_0
    | ~ r2_hidden(X1,k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( esk9_0 = esk8_0
    | r2_hidden(esk8_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_55])).

cnf(c_0_59,plain,
    ( k4_tarski(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0) = k1_xboole_0
    | r2_hidden(esk8_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_29]),c_0_22])]),c_0_58])).

cnf(c_0_61,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_62,plain,
    ( k4_tarski(esk2_4(k1_xboole_0,X1,k1_xboole_0,X2),esk3_4(k1_xboole_0,X1,k1_xboole_0,X2)) = X2
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_46])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk8_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_60]),c_0_46])])).

cnf(c_0_64,plain,
    ( r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( k4_tarski(esk2_4(k1_xboole_0,X1,k1_xboole_0,esk8_0),esk3_4(k1_xboole_0,X1,k1_xboole_0,esk8_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,plain,
    ( r2_hidden(esk3_4(k1_xboole_0,X1,k1_xboole_0,X2),X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_46])).

fof(c_0_67,plain,(
    ! [X39,X40] :
      ( ( k4_xboole_0(k1_tarski(X39),k1_tarski(X40)) != k1_tarski(X39)
        | X39 != X40 )
      & ( X39 = X40
        | k4_xboole_0(k1_tarski(X39),k1_tarski(X40)) = k1_tarski(X39) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_68,negated_conjecture,
    ( esk2_4(k1_xboole_0,X1,k1_xboole_0,esk8_0) = esk9_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_65]),c_0_44])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk3_4(k1_xboole_0,X1,k1_xboole_0,esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_63])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( k4_tarski(esk9_0,esk3_4(k1_xboole_0,X1,k1_xboole_0,esk8_0)) = esk8_0 ),
    inference(rw,[status(thm)],[c_0_65,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( esk3_4(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k1_xboole_0,esk8_0) = X1 ),
    inference(spm,[status(thm)],[c_0_37,c_0_69])).

cnf(c_0_73,plain,
    ( X1 != X2
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_16]),c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_74,negated_conjecture,
    ( k4_tarski(esk9_0,X1) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( esk10_0 = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_74]),c_0_49])).

cnf(c_0_77,plain,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76]),c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:25:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 15.00/15.22  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 15.00/15.22  # and selection function SelectNegativeLiterals.
% 15.00/15.22  #
% 15.00/15.22  # Preprocessing time       : 0.028 s
% 15.00/15.22  # Presaturation interreduction done
% 15.00/15.22  
% 15.00/15.22  # Proof found!
% 15.00/15.22  # SZS status Theorem
% 15.00/15.22  # SZS output start CNFRefutation
% 15.00/15.22  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 15.00/15.22  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 15.00/15.22  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 15.00/15.22  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 15.00/15.22  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 15.00/15.22  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 15.00/15.22  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 15.00/15.22  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 15.00/15.22  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 15.00/15.22  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 15.00/15.22  fof(c_0_10, plain, ![X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X9,X8)|X9=X7|X8!=k1_tarski(X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k1_tarski(X7)))&((~r2_hidden(esk1_2(X11,X12),X12)|esk1_2(X11,X12)!=X11|X12=k1_tarski(X11))&(r2_hidden(esk1_2(X11,X12),X12)|esk1_2(X11,X12)=X11|X12=k1_tarski(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 15.00/15.22  fof(c_0_11, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 15.00/15.22  fof(c_0_12, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 15.00/15.22  fof(c_0_13, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 15.00/15.22  fof(c_0_14, plain, ![X20, X21, X22, X23, X26, X27, X28, X29, X30, X31, X33, X34]:(((((r2_hidden(esk2_4(X20,X21,X22,X23),X20)|~r2_hidden(X23,X22)|X22!=k2_zfmisc_1(X20,X21))&(r2_hidden(esk3_4(X20,X21,X22,X23),X21)|~r2_hidden(X23,X22)|X22!=k2_zfmisc_1(X20,X21)))&(X23=k4_tarski(esk2_4(X20,X21,X22,X23),esk3_4(X20,X21,X22,X23))|~r2_hidden(X23,X22)|X22!=k2_zfmisc_1(X20,X21)))&(~r2_hidden(X27,X20)|~r2_hidden(X28,X21)|X26!=k4_tarski(X27,X28)|r2_hidden(X26,X22)|X22!=k2_zfmisc_1(X20,X21)))&((~r2_hidden(esk4_3(X29,X30,X31),X31)|(~r2_hidden(X33,X29)|~r2_hidden(X34,X30)|esk4_3(X29,X30,X31)!=k4_tarski(X33,X34))|X31=k2_zfmisc_1(X29,X30))&(((r2_hidden(esk5_3(X29,X30,X31),X29)|r2_hidden(esk4_3(X29,X30,X31),X31)|X31=k2_zfmisc_1(X29,X30))&(r2_hidden(esk6_3(X29,X30,X31),X30)|r2_hidden(esk4_3(X29,X30,X31),X31)|X31=k2_zfmisc_1(X29,X30)))&(esk4_3(X29,X30,X31)=k4_tarski(esk5_3(X29,X30,X31),esk6_3(X29,X30,X31))|r2_hidden(esk4_3(X29,X30,X31),X31)|X31=k2_zfmisc_1(X29,X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 15.00/15.22  cnf(c_0_15, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 15.00/15.22  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 15.00/15.22  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 15.00/15.22  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 15.00/15.22  cnf(c_0_19, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 15.00/15.22  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 15.00/15.22  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])])).
% 15.00/15.22  cnf(c_0_22, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).
% 15.00/15.22  fof(c_0_23, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 15.00/15.22  cnf(c_0_24, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X3))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 15.00/15.22  fof(c_0_25, negated_conjecture, (esk8_0=k4_tarski(esk9_0,esk10_0)&(esk8_0=k1_mcart_1(esk8_0)|esk8_0=k2_mcart_1(esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 15.00/15.22  fof(c_0_26, plain, ![X37, X38]:((k2_zfmisc_1(X37,X38)!=k1_xboole_0|(X37=k1_xboole_0|X38=k1_xboole_0))&((X37!=k1_xboole_0|k2_zfmisc_1(X37,X38)=k1_xboole_0)&(X38!=k1_xboole_0|k2_zfmisc_1(X37,X38)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 15.00/15.22  cnf(c_0_27, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 15.00/15.22  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 15.00/15.22  cnf(c_0_29, negated_conjecture, (esk8_0=k4_tarski(esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 15.00/15.22  fof(c_0_30, plain, ![X43, X45, X46]:((r2_hidden(esk7_1(X43),X43)|X43=k1_xboole_0)&((~r2_hidden(X45,X43)|esk7_1(X43)!=k4_tarski(X45,X46)|X43=k1_xboole_0)&(~r2_hidden(X46,X43)|esk7_1(X43)!=k4_tarski(X45,X46)|X43=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 15.00/15.22  cnf(c_0_31, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 15.00/15.22  cnf(c_0_32, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_16]), c_0_17]), c_0_18])).
% 15.00/15.22  cnf(c_0_33, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0),k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 15.00/15.22  cnf(c_0_34, plain, (r2_hidden(esk7_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 15.00/15.22  cnf(c_0_35, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_31])).
% 15.00/15.22  fof(c_0_36, plain, ![X41, X42]:(k1_mcart_1(k4_tarski(X41,X42))=X41&k2_mcart_1(k4_tarski(X41,X42))=X42), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 15.00/15.22  cnf(c_0_37, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_32])).
% 15.00/15.22  cnf(c_0_38, negated_conjecture, (r2_hidden(esk7_1(k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0)),k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0))|r2_hidden(esk8_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 15.00/15.22  cnf(c_0_39, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 15.00/15.22  cnf(c_0_40, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 15.00/15.22  cnf(c_0_41, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk7_1(X2)!=k4_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 15.00/15.22  cnf(c_0_42, negated_conjecture, (esk7_1(k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0))=esk10_0|r2_hidden(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 15.00/15.22  cnf(c_0_43, negated_conjecture, (esk8_0=k1_mcart_1(esk8_0)|esk8_0=k2_mcart_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 15.00/15.22  cnf(c_0_44, negated_conjecture, (k1_mcart_1(esk8_0)=esk9_0), inference(spm,[status(thm)],[c_0_39, c_0_29])).
% 15.00/15.22  cnf(c_0_45, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_36])).
% 15.00/15.22  cnf(c_0_46, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_40])).
% 15.00/15.22  cnf(c_0_47, negated_conjecture, (k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0)=k1_xboole_0|r2_hidden(esk8_0,k1_xboole_0)|k4_tarski(X1,X2)!=esk10_0|~r2_hidden(X2,k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 15.00/15.22  cnf(c_0_48, negated_conjecture, (k2_mcart_1(esk8_0)=esk8_0|esk9_0=esk8_0), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 15.00/15.22  cnf(c_0_49, negated_conjecture, (k2_mcart_1(esk8_0)=esk10_0), inference(spm,[status(thm)],[c_0_45, c_0_29])).
% 15.00/15.22  cnf(c_0_50, negated_conjecture, (r2_hidden(esk7_1(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)),k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))|r2_hidden(esk8_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_46])).
% 15.00/15.22  cnf(c_0_51, negated_conjecture, (k2_enumset1(esk10_0,esk10_0,esk10_0,esk10_0)=k1_xboole_0|r2_hidden(esk8_0,k1_xboole_0)|esk10_0!=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_29]), c_0_22])])).
% 15.00/15.22  cnf(c_0_52, negated_conjecture, (esk9_0=esk8_0|esk10_0=esk8_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 15.00/15.22  cnf(c_0_53, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk7_1(X2)!=k4_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 15.00/15.22  cnf(c_0_54, negated_conjecture, (esk7_1(k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))=esk9_0|r2_hidden(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_50])).
% 15.00/15.22  cnf(c_0_55, negated_conjecture, (k2_enumset1(esk8_0,esk8_0,esk8_0,esk8_0)=k1_xboole_0|esk9_0=esk8_0|r2_hidden(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 15.00/15.22  cnf(c_0_56, plain, (X1=k4_tarski(esk2_4(X2,X3,X4,X1),esk3_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 15.00/15.22  cnf(c_0_57, negated_conjecture, (k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)=k1_xboole_0|r2_hidden(esk8_0,k1_xboole_0)|k4_tarski(X1,X2)!=esk9_0|~r2_hidden(X1,k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 15.00/15.22  cnf(c_0_58, negated_conjecture, (esk9_0=esk8_0|r2_hidden(esk8_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_55])).
% 15.00/15.22  cnf(c_0_59, plain, (k4_tarski(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3))=X3|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_56])).
% 15.00/15.22  cnf(c_0_60, negated_conjecture, (k2_enumset1(esk9_0,esk9_0,esk9_0,esk9_0)=k1_xboole_0|r2_hidden(esk8_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_29]), c_0_22])]), c_0_58])).
% 15.00/15.22  cnf(c_0_61, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 15.00/15.22  cnf(c_0_62, plain, (k4_tarski(esk2_4(k1_xboole_0,X1,k1_xboole_0,X2),esk3_4(k1_xboole_0,X1,k1_xboole_0,X2))=X2|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_59, c_0_46])).
% 15.00/15.22  cnf(c_0_63, negated_conjecture, (r2_hidden(esk8_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_60]), c_0_46])])).
% 15.00/15.22  cnf(c_0_64, plain, (r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_61])).
% 15.00/15.22  cnf(c_0_65, negated_conjecture, (k4_tarski(esk2_4(k1_xboole_0,X1,k1_xboole_0,esk8_0),esk3_4(k1_xboole_0,X1,k1_xboole_0,esk8_0))=esk8_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 15.00/15.22  cnf(c_0_66, plain, (r2_hidden(esk3_4(k1_xboole_0,X1,k1_xboole_0,X2),X1)|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_46])).
% 15.00/15.22  fof(c_0_67, plain, ![X39, X40]:((k4_xboole_0(k1_tarski(X39),k1_tarski(X40))!=k1_tarski(X39)|X39!=X40)&(X39=X40|k4_xboole_0(k1_tarski(X39),k1_tarski(X40))=k1_tarski(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 15.00/15.22  cnf(c_0_68, negated_conjecture, (esk2_4(k1_xboole_0,X1,k1_xboole_0,esk8_0)=esk9_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_65]), c_0_44])).
% 15.00/15.22  cnf(c_0_69, negated_conjecture, (r2_hidden(esk3_4(k1_xboole_0,X1,k1_xboole_0,esk8_0),X1)), inference(spm,[status(thm)],[c_0_66, c_0_63])).
% 15.00/15.22  cnf(c_0_70, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_67])).
% 15.00/15.22  cnf(c_0_71, negated_conjecture, (k4_tarski(esk9_0,esk3_4(k1_xboole_0,X1,k1_xboole_0,esk8_0))=esk8_0), inference(rw,[status(thm)],[c_0_65, c_0_68])).
% 15.00/15.22  cnf(c_0_72, negated_conjecture, (esk3_4(k1_xboole_0,k2_enumset1(X1,X1,X1,X1),k1_xboole_0,esk8_0)=X1), inference(spm,[status(thm)],[c_0_37, c_0_69])).
% 15.00/15.22  cnf(c_0_73, plain, (X1!=X2|k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))!=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_16]), c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_18])).
% 15.00/15.22  cnf(c_0_74, negated_conjecture, (k4_tarski(esk9_0,X1)=esk8_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 15.00/15.22  cnf(c_0_75, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))!=k2_enumset1(X1,X1,X1,X1)), inference(er,[status(thm)],[c_0_73])).
% 15.00/15.22  cnf(c_0_76, negated_conjecture, (esk10_0=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_74]), c_0_49])).
% 15.00/15.22  cnf(c_0_77, plain, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76]), c_0_76])]), ['proof']).
% 15.00/15.22  # SZS output end CNFRefutation
% 15.00/15.22  # Proof object total steps             : 78
% 15.00/15.22  # Proof object clause steps            : 57
% 15.00/15.22  # Proof object formula steps           : 21
% 15.00/15.22  # Proof object conjectures             : 28
% 15.00/15.22  # Proof object clause conjectures      : 25
% 15.00/15.22  # Proof object formula conjectures     : 3
% 15.00/15.22  # Proof object initial clauses used    : 18
% 15.00/15.22  # Proof object initial formulas used   : 10
% 15.00/15.22  # Proof object generating inferences   : 25
% 15.00/15.22  # Proof object simplifying inferences  : 41
% 15.00/15.22  # Training examples: 0 positive, 0 negative
% 15.00/15.22  # Parsed axioms                        : 10
% 15.00/15.22  # Removed by relevancy pruning/SinE    : 0
% 15.00/15.22  # Initial clauses                      : 27
% 15.00/15.22  # Removed in clause preprocessing      : 3
% 15.00/15.22  # Initial clauses in saturation        : 24
% 15.00/15.22  # Processed clauses                    : 13535
% 15.00/15.22  # ...of these trivial                  : 152
% 15.00/15.22  # ...subsumed                          : 10386
% 15.00/15.22  # ...remaining for further processing  : 2997
% 15.00/15.22  # Other redundant clauses eliminated   : 131380
% 15.00/15.22  # Clauses deleted for lack of memory   : 0
% 15.00/15.22  # Backward-subsumed                    : 316
% 15.00/15.22  # Backward-rewritten                   : 2645
% 15.00/15.22  # Generated clauses                    : 2276293
% 15.00/15.22  # ...of the previous two non-trivial   : 2062969
% 15.00/15.22  # Contextual simplify-reflections      : 29
% 15.00/15.22  # Paramodulations                      : 2144030
% 15.00/15.22  # Factorizations                       : 881
% 15.00/15.22  # Equation resolutions                 : 131384
% 15.00/15.22  # Propositional unsat checks           : 0
% 15.00/15.22  #    Propositional check models        : 0
% 15.00/15.22  #    Propositional check unsatisfiable : 0
% 15.00/15.22  #    Propositional clauses             : 0
% 15.00/15.22  #    Propositional clauses after purity: 0
% 15.00/15.22  #    Propositional unsat core size     : 0
% 15.00/15.22  #    Propositional preprocessing time  : 0.000
% 15.00/15.22  #    Propositional encoding time       : 0.000
% 15.00/15.22  #    Propositional solver time         : 0.000
% 15.00/15.22  #    Success case prop preproc time    : 0.000
% 15.00/15.22  #    Success case prop encoding time   : 0.000
% 15.00/15.22  #    Success case prop solver time     : 0.000
% 15.00/15.22  # Current number of processed clauses  : 3
% 15.00/15.22  #    Positive orientable unit clauses  : 2
% 15.00/15.22  #    Positive unorientable unit clauses: 1
% 15.00/15.22  #    Negative unit clauses             : 0
% 15.00/15.22  #    Non-unit-clauses                  : 0
% 15.00/15.22  # Current number of unprocessed clauses: 2047558
% 15.00/15.22  # ...number of literals in the above   : 12904437
% 15.00/15.22  # Current number of archived formulas  : 0
% 15.00/15.22  # Current number of archived clauses   : 2988
% 15.00/15.22  # Clause-clause subsumption calls (NU) : 1308322
% 15.00/15.22  # Rec. Clause-clause subsumption calls : 82958
% 15.00/15.22  # Non-unit clause-clause subsumptions  : 10700
% 15.00/15.22  # Unit Clause-clause subsumption calls : 24689
% 15.00/15.22  # Rewrite failures with RHS unbound    : 3
% 15.00/15.22  # BW rewrite match attempts            : 2106
% 15.00/15.22  # BW rewrite match successes           : 1482
% 15.00/15.22  # Condensation attempts                : 0
% 15.00/15.22  # Condensation successes               : 0
% 15.00/15.22  # Termbank termtop insertions          : 53256441
% 15.10/15.30  
% 15.10/15.30  # -------------------------------------------------
% 15.10/15.30  # User time                : 14.195 s
% 15.10/15.30  # System time              : 0.749 s
% 15.10/15.30  # Total time               : 14.945 s
% 15.10/15.30  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
