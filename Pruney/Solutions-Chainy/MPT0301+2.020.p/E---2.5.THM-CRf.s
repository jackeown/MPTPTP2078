%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:27 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   75 (5099 expanded)
%              Number of clauses        :   62 (2648 expanded)
%              Number of leaves         :    6 (1223 expanded)
%              Depth                    :   21
%              Number of atoms          :  206 (19286 expanded)
%              Number of equality atoms :  116 (8670 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_6,plain,(
    ! [X37,X38] :
      ( ( k4_xboole_0(X37,k1_tarski(X38)) != X37
        | ~ r2_hidden(X38,X37) )
      & ( r2_hidden(X38,X37)
        | k4_xboole_0(X37,k1_tarski(X38)) = X37 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_7,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_8,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X9,X10,X11,X12,X15,X16,X17,X18,X19,X20,X22,X23] :
      ( ( r2_hidden(esk1_4(X9,X10,X11,X12),X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k2_zfmisc_1(X9,X10) )
      & ( r2_hidden(esk2_4(X9,X10,X11,X12),X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k2_zfmisc_1(X9,X10) )
      & ( X12 = k4_tarski(esk1_4(X9,X10,X11,X12),esk2_4(X9,X10,X11,X12))
        | ~ r2_hidden(X12,X11)
        | X11 != k2_zfmisc_1(X9,X10) )
      & ( ~ r2_hidden(X16,X9)
        | ~ r2_hidden(X17,X10)
        | X15 != k4_tarski(X16,X17)
        | r2_hidden(X15,X11)
        | X11 != k2_zfmisc_1(X9,X10) )
      & ( ~ r2_hidden(esk3_3(X18,X19,X20),X20)
        | ~ r2_hidden(X22,X18)
        | ~ r2_hidden(X23,X19)
        | esk3_3(X18,X19,X20) != k4_tarski(X22,X23)
        | X20 = k2_zfmisc_1(X18,X19) )
      & ( r2_hidden(esk4_3(X18,X19,X20),X18)
        | r2_hidden(esk3_3(X18,X19,X20),X20)
        | X20 = k2_zfmisc_1(X18,X19) )
      & ( r2_hidden(esk5_3(X18,X19,X20),X19)
        | r2_hidden(esk3_3(X18,X19,X20),X20)
        | X20 = k2_zfmisc_1(X18,X19) )
      & ( esk3_3(X18,X19,X20) = k4_tarski(esk4_3(X18,X19,X20),esk5_3(X18,X19,X20))
        | r2_hidden(esk3_3(X18,X19,X20),X20)
        | X20 = k2_zfmisc_1(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k2_tarski(X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X7] : k4_xboole_0(k1_xboole_0,X7) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k2_tarski(esk1_4(X1,X2,X3,X4),esk1_4(X1,X2,X3,X4))) != X1
    | X3 != k2_zfmisc_1(X1,X2)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X26,X27,X28,X30,X31,X32,X33,X35] :
      ( ( r2_hidden(X28,esk6_3(X26,X27,X28))
        | ~ r2_hidden(X28,X27)
        | X27 != k3_tarski(X26) )
      & ( r2_hidden(esk6_3(X26,X27,X28),X26)
        | ~ r2_hidden(X28,X27)
        | X27 != k3_tarski(X26) )
      & ( ~ r2_hidden(X30,X31)
        | ~ r2_hidden(X31,X26)
        | r2_hidden(X30,X27)
        | X27 != k3_tarski(X26) )
      & ( ~ r2_hidden(esk7_2(X32,X33),X33)
        | ~ r2_hidden(esk7_2(X32,X33),X35)
        | ~ r2_hidden(X35,X32)
        | X33 = k3_tarski(X32) )
      & ( r2_hidden(esk7_2(X32,X33),esk8_2(X32,X33))
        | r2_hidden(esk7_2(X32,X33),X33)
        | X33 = k3_tarski(X32) )
      & ( r2_hidden(esk8_2(X32,X33),X32)
        | r2_hidden(esk7_2(X32,X33),X33)
        | X33 = k3_tarski(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_17,plain,
    ( X1 != k2_zfmisc_1(k1_xboole_0,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k2_tarski(esk6_3(X1,X2,X3),esk6_3(X1,X2,X3))) != X1
    | X2 != k3_tarski(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_18])).

cnf(c_0_21,plain,
    ( X1 != k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_22,plain,
    ( X1 != k3_tarski(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_23,plain,
    ( r2_hidden(esk8_2(X1,X2),X1)
    | r2_hidden(esk7_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( X1 = k3_tarski(X2)
    | r2_hidden(esk7_2(X2,X1),X1)
    | X2 != k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( X1 != k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_27,plain,
    ( X1 = k3_tarski(X2)
    | X1 != k3_tarski(k1_xboole_0)
    | X2 != k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_25])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)))) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_29,plain,
    ( k3_tarski(k1_xboole_0) = k3_tarski(X1)
    | X1 != k3_tarski(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_30,plain,
    ( X1 != k3_tarski(k1_xboole_0)
    | X2 != k2_zfmisc_1(X1,X3)
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_12])).

cnf(c_0_31,plain,
    ( X1 != k2_zfmisc_1(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))),X3)
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_12])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k3_tarski(X2)
    | X2 != k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_25])).

cnf(c_0_33,plain,
    ( k3_tarski(k3_tarski(k1_xboole_0)) = k3_tarski(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,plain,
    ( X1 != k3_tarski(k1_xboole_0)
    | ~ r2_hidden(X2,k2_zfmisc_1(X1,X3)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))),X3)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k3_tarski(k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_33])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_39,plain,
    ( X1 != k3_tarski(k1_xboole_0)
    | X2 != k2_zfmisc_1(X3,X1)
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_34])).

cnf(c_0_40,plain,
    ( X1 = k3_tarski(X2)
    | r2_hidden(esk7_2(X2,X1),X1)
    | k4_xboole_0(X2,k2_tarski(esk8_2(X2,X1),esk8_2(X2,X1))) != X2 ),
    inference(spm,[status(thm)],[c_0_11,c_0_23])).

cnf(c_0_41,plain,
    ( X1 = k3_tarski(k2_zfmisc_1(X2,X3))
    | r2_hidden(esk7_2(k2_zfmisc_1(X2,X3),X1),X1)
    | X2 != k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_23])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k3_tarski(k1_xboole_0),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_33]),c_0_33])).

cnf(c_0_43,plain,
    ( X1 != k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_18])).

fof(c_0_44,negated_conjecture,
    ( ( esk9_0 != k1_xboole_0
      | k2_zfmisc_1(esk9_0,esk10_0) != k1_xboole_0 )
    & ( esk10_0 != k1_xboole_0
      | k2_zfmisc_1(esk9_0,esk10_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk9_0,esk10_0) = k1_xboole_0
      | esk9_0 = k1_xboole_0
      | esk10_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])])).

cnf(c_0_45,plain,
    ( X1 != k3_tarski(k1_xboole_0)
    | ~ r2_hidden(X2,k2_zfmisc_1(X3,X1)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( X1 = k3_tarski(k1_xboole_0)
    | r2_hidden(esk7_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_15])).

cnf(c_0_47,plain,
    ( X1 = k3_tarski(k2_zfmisc_1(X2,X3))
    | k4_xboole_0(X1,k2_tarski(esk7_2(k2_zfmisc_1(X2,X3),X1),esk7_2(k2_zfmisc_1(X2,X3),X1))) != X1
    | X2 != k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_41])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(k3_tarski(k1_xboole_0),X1) = k3_tarski(X2)
    | X2 != k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_25])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))))) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( esk10_0 != k1_xboole_0
    | k2_zfmisc_1(esk9_0,esk10_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(X1,X2) = k3_tarski(k1_xboole_0)
    | X2 != k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( k3_tarski(k2_zfmisc_1(X1,X2)) = k1_xboole_0
    | X1 != k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_15])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(k3_tarski(k1_xboole_0),X1) = k3_tarski(k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_33])).

cnf(c_0_54,negated_conjecture,
    ( esk9_0 != k1_xboole_0
    | k2_zfmisc_1(esk9_0,esk10_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(X1,X2) = k3_tarski(k1_xboole_0)
    | X1 != k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_46])).

cnf(c_0_56,plain,
    ( X1 != k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)))))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_18])).

cnf(c_0_57,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_58,negated_conjecture,
    ( k3_tarski(k1_xboole_0) != k1_xboole_0
    | esk10_0 != k3_tarski(k1_xboole_0)
    | esk10_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_33])).

cnf(c_0_60,negated_conjecture,
    ( k3_tarski(k1_xboole_0) != k1_xboole_0
    | esk9_0 != k3_tarski(k1_xboole_0)
    | esk9_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)))))) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | X1 != k4_tarski(X4,X5)
    | ~ r2_hidden(X5,X3)
    | ~ r2_hidden(X4,X2) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( k2_zfmisc_1(esk9_0,esk10_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_64,negated_conjecture,
    ( esk10_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_59])])).

cnf(c_0_65,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_59]),c_0_59])])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k3_tarski(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_37]),c_0_33]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_67,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( k2_zfmisc_1(esk9_0,esk10_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_66,c_0_59])).

cnf(c_0_70,plain,
    ( X1 = k3_tarski(k1_xboole_0)
    | r2_hidden(esk7_2(k3_tarski(k1_xboole_0),X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_23]),c_0_33])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(X1,esk10_0)
    | ~ r2_hidden(X2,esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk7_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_59]),c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_hidden(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_72]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:06:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.69/0.88  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.69/0.88  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.69/0.88  #
% 0.69/0.88  # Preprocessing time       : 0.028 s
% 0.69/0.88  # Presaturation interreduction done
% 0.69/0.88  
% 0.69/0.88  # Proof found!
% 0.69/0.88  # SZS status Theorem
% 0.69/0.88  # SZS output start CNFRefutation
% 0.69/0.88  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.69/0.88  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.69/0.88  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.69/0.88  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.69/0.88  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.69/0.88  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.69/0.88  fof(c_0_6, plain, ![X37, X38]:((k4_xboole_0(X37,k1_tarski(X38))!=X37|~r2_hidden(X38,X37))&(r2_hidden(X38,X37)|k4_xboole_0(X37,k1_tarski(X38))=X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.69/0.88  fof(c_0_7, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.69/0.88  cnf(c_0_8, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.69/0.88  cnf(c_0_9, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.69/0.88  fof(c_0_10, plain, ![X9, X10, X11, X12, X15, X16, X17, X18, X19, X20, X22, X23]:(((((r2_hidden(esk1_4(X9,X10,X11,X12),X9)|~r2_hidden(X12,X11)|X11!=k2_zfmisc_1(X9,X10))&(r2_hidden(esk2_4(X9,X10,X11,X12),X10)|~r2_hidden(X12,X11)|X11!=k2_zfmisc_1(X9,X10)))&(X12=k4_tarski(esk1_4(X9,X10,X11,X12),esk2_4(X9,X10,X11,X12))|~r2_hidden(X12,X11)|X11!=k2_zfmisc_1(X9,X10)))&(~r2_hidden(X16,X9)|~r2_hidden(X17,X10)|X15!=k4_tarski(X16,X17)|r2_hidden(X15,X11)|X11!=k2_zfmisc_1(X9,X10)))&((~r2_hidden(esk3_3(X18,X19,X20),X20)|(~r2_hidden(X22,X18)|~r2_hidden(X23,X19)|esk3_3(X18,X19,X20)!=k4_tarski(X22,X23))|X20=k2_zfmisc_1(X18,X19))&(((r2_hidden(esk4_3(X18,X19,X20),X18)|r2_hidden(esk3_3(X18,X19,X20),X20)|X20=k2_zfmisc_1(X18,X19))&(r2_hidden(esk5_3(X18,X19,X20),X19)|r2_hidden(esk3_3(X18,X19,X20),X20)|X20=k2_zfmisc_1(X18,X19)))&(esk3_3(X18,X19,X20)=k4_tarski(esk4_3(X18,X19,X20),esk5_3(X18,X19,X20))|r2_hidden(esk3_3(X18,X19,X20),X20)|X20=k2_zfmisc_1(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.69/0.88  cnf(c_0_11, plain, (k4_xboole_0(X1,k2_tarski(X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.69/0.88  cnf(c_0_12, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.69/0.88  fof(c_0_13, plain, ![X7]:k4_xboole_0(k1_xboole_0,X7)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.69/0.88  cnf(c_0_14, plain, (k4_xboole_0(X1,k2_tarski(esk1_4(X1,X2,X3,X4),esk1_4(X1,X2,X3,X4)))!=X1|X3!=k2_zfmisc_1(X1,X2)|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.69/0.88  cnf(c_0_15, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.69/0.88  fof(c_0_16, plain, ![X26, X27, X28, X30, X31, X32, X33, X35]:((((r2_hidden(X28,esk6_3(X26,X27,X28))|~r2_hidden(X28,X27)|X27!=k3_tarski(X26))&(r2_hidden(esk6_3(X26,X27,X28),X26)|~r2_hidden(X28,X27)|X27!=k3_tarski(X26)))&(~r2_hidden(X30,X31)|~r2_hidden(X31,X26)|r2_hidden(X30,X27)|X27!=k3_tarski(X26)))&((~r2_hidden(esk7_2(X32,X33),X33)|(~r2_hidden(esk7_2(X32,X33),X35)|~r2_hidden(X35,X32))|X33=k3_tarski(X32))&((r2_hidden(esk7_2(X32,X33),esk8_2(X32,X33))|r2_hidden(esk7_2(X32,X33),X33)|X33=k3_tarski(X32))&(r2_hidden(esk8_2(X32,X33),X32)|r2_hidden(esk7_2(X32,X33),X33)|X33=k3_tarski(X32))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.69/0.88  cnf(c_0_17, plain, (X1!=k2_zfmisc_1(k1_xboole_0,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.69/0.88  cnf(c_0_18, plain, (r2_hidden(esk6_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.69/0.88  cnf(c_0_19, plain, (~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.69/0.88  cnf(c_0_20, plain, (k4_xboole_0(X1,k2_tarski(esk6_3(X1,X2,X3),esk6_3(X1,X2,X3)))!=X1|X2!=k3_tarski(X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_11, c_0_18])).
% 0.69/0.88  cnf(c_0_21, plain, (X1!=k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.69/0.88  cnf(c_0_22, plain, (X1!=k3_tarski(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_15])).
% 0.69/0.88  cnf(c_0_23, plain, (r2_hidden(esk8_2(X1,X2),X1)|r2_hidden(esk7_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.69/0.88  cnf(c_0_24, plain, (~r2_hidden(X1,k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)))), inference(er,[status(thm)],[c_0_21])).
% 0.69/0.88  cnf(c_0_25, plain, (X1=k3_tarski(X2)|r2_hidden(esk7_2(X2,X1),X1)|X2!=k3_tarski(k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.69/0.88  cnf(c_0_26, plain, (X1!=k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_24, c_0_18])).
% 0.69/0.88  cnf(c_0_27, plain, (X1=k3_tarski(X2)|X1!=k3_tarski(k1_xboole_0)|X2!=k3_tarski(k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_25])).
% 0.69/0.88  cnf(c_0_28, plain, (~r2_hidden(X1,k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))))), inference(er,[status(thm)],[c_0_26])).
% 0.69/0.88  cnf(c_0_29, plain, (k3_tarski(k1_xboole_0)=k3_tarski(X1)|X1!=k3_tarski(k1_xboole_0)), inference(er,[status(thm)],[c_0_27])).
% 0.69/0.88  cnf(c_0_30, plain, (X1!=k3_tarski(k1_xboole_0)|X2!=k2_zfmisc_1(X1,X3)|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_22, c_0_12])).
% 0.69/0.88  cnf(c_0_31, plain, (X1!=k2_zfmisc_1(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))),X3)|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_28, c_0_12])).
% 0.69/0.88  cnf(c_0_32, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k3_tarski(X2)|X2!=k3_tarski(k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_25])).
% 0.69/0.88  cnf(c_0_33, plain, (k3_tarski(k3_tarski(k1_xboole_0))=k3_tarski(k1_xboole_0)), inference(er,[status(thm)],[c_0_29])).
% 0.69/0.88  cnf(c_0_34, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.69/0.88  cnf(c_0_35, plain, (X1!=k3_tarski(k1_xboole_0)|~r2_hidden(X2,k2_zfmisc_1(X1,X3))), inference(er,[status(thm)],[c_0_30])).
% 0.69/0.88  cnf(c_0_36, plain, (~r2_hidden(X1,k2_zfmisc_1(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))),X3))), inference(er,[status(thm)],[c_0_31])).
% 0.69/0.88  cnf(c_0_37, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k3_tarski(k1_xboole_0)), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_33])).
% 0.69/0.88  fof(c_0_38, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.69/0.88  cnf(c_0_39, plain, (X1!=k3_tarski(k1_xboole_0)|X2!=k2_zfmisc_1(X3,X1)|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_22, c_0_34])).
% 0.69/0.88  cnf(c_0_40, plain, (X1=k3_tarski(X2)|r2_hidden(esk7_2(X2,X1),X1)|k4_xboole_0(X2,k2_tarski(esk8_2(X2,X1),esk8_2(X2,X1)))!=X2), inference(spm,[status(thm)],[c_0_11, c_0_23])).
% 0.69/0.88  cnf(c_0_41, plain, (X1=k3_tarski(k2_zfmisc_1(X2,X3))|r2_hidden(esk7_2(k2_zfmisc_1(X2,X3),X1),X1)|X2!=k3_tarski(k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_23])).
% 0.69/0.88  cnf(c_0_42, plain, (~r2_hidden(X1,k2_zfmisc_1(k3_tarski(k1_xboole_0),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_33]), c_0_33])).
% 0.69/0.88  cnf(c_0_43, plain, (X1!=k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_28, c_0_18])).
% 0.69/0.88  fof(c_0_44, negated_conjecture, (((esk9_0!=k1_xboole_0|k2_zfmisc_1(esk9_0,esk10_0)!=k1_xboole_0)&(esk10_0!=k1_xboole_0|k2_zfmisc_1(esk9_0,esk10_0)!=k1_xboole_0))&(k2_zfmisc_1(esk9_0,esk10_0)=k1_xboole_0|(esk9_0=k1_xboole_0|esk10_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])])).
% 0.69/0.88  cnf(c_0_45, plain, (X1!=k3_tarski(k1_xboole_0)|~r2_hidden(X2,k2_zfmisc_1(X3,X1))), inference(er,[status(thm)],[c_0_39])).
% 0.69/0.88  cnf(c_0_46, plain, (X1=k3_tarski(k1_xboole_0)|r2_hidden(esk7_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_40, c_0_15])).
% 0.69/0.88  cnf(c_0_47, plain, (X1=k3_tarski(k2_zfmisc_1(X2,X3))|k4_xboole_0(X1,k2_tarski(esk7_2(k2_zfmisc_1(X2,X3),X1),esk7_2(k2_zfmisc_1(X2,X3),X1)))!=X1|X2!=k3_tarski(k1_xboole_0)), inference(spm,[status(thm)],[c_0_11, c_0_41])).
% 0.69/0.88  cnf(c_0_48, plain, (k2_zfmisc_1(k3_tarski(k1_xboole_0),X1)=k3_tarski(X2)|X2!=k3_tarski(k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_25])).
% 0.69/0.88  cnf(c_0_49, plain, (~r2_hidden(X1,k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)))))), inference(er,[status(thm)],[c_0_43])).
% 0.69/0.88  cnf(c_0_50, negated_conjecture, (esk10_0!=k1_xboole_0|k2_zfmisc_1(esk9_0,esk10_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.69/0.88  cnf(c_0_51, plain, (k2_zfmisc_1(X1,X2)=k3_tarski(k1_xboole_0)|X2!=k3_tarski(k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.69/0.88  cnf(c_0_52, plain, (k3_tarski(k2_zfmisc_1(X1,X2))=k1_xboole_0|X1!=k3_tarski(k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_15])).
% 0.69/0.88  cnf(c_0_53, plain, (k2_zfmisc_1(k3_tarski(k1_xboole_0),X1)=k3_tarski(k1_xboole_0)), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]), c_0_33])).
% 0.69/0.88  cnf(c_0_54, negated_conjecture, (esk9_0!=k1_xboole_0|k2_zfmisc_1(esk9_0,esk10_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.69/0.88  cnf(c_0_55, plain, (k2_zfmisc_1(X1,X2)=k3_tarski(k1_xboole_0)|X1!=k3_tarski(k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_46])).
% 0.69/0.88  cnf(c_0_56, plain, (X1!=k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2)))))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_49, c_0_18])).
% 0.69/0.88  cnf(c_0_57, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.69/0.88  cnf(c_0_58, negated_conjecture, (k3_tarski(k1_xboole_0)!=k1_xboole_0|esk10_0!=k3_tarski(k1_xboole_0)|esk10_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.69/0.88  cnf(c_0_59, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_33])).
% 0.69/0.88  cnf(c_0_60, negated_conjecture, (k3_tarski(k1_xboole_0)!=k1_xboole_0|esk9_0!=k3_tarski(k1_xboole_0)|esk9_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.69/0.88  cnf(c_0_61, plain, (~r2_hidden(X1,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k2_zfmisc_1(k1_xboole_0,X2))))))), inference(er,[status(thm)],[c_0_56])).
% 0.69/0.88  cnf(c_0_62, plain, (r2_hidden(X1,k2_zfmisc_1(X2,X3))|X1!=k4_tarski(X4,X5)|~r2_hidden(X5,X3)|~r2_hidden(X4,X2)), inference(er,[status(thm)],[c_0_57])).
% 0.69/0.88  cnf(c_0_63, negated_conjecture, (k2_zfmisc_1(esk9_0,esk10_0)=k1_xboole_0|esk9_0=k1_xboole_0|esk10_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.69/0.88  cnf(c_0_64, negated_conjecture, (esk10_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_59])])).
% 0.69/0.88  cnf(c_0_65, negated_conjecture, (esk9_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_59]), c_0_59])])).
% 0.69/0.88  cnf(c_0_66, plain, (~r2_hidden(X1,k3_tarski(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_37]), c_0_33]), c_0_33]), c_0_33]), c_0_33])).
% 0.69/0.88  cnf(c_0_67, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_62])).
% 0.69/0.88  cnf(c_0_68, negated_conjecture, (k2_zfmisc_1(esk9_0,esk10_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.69/0.88  cnf(c_0_69, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_66, c_0_59])).
% 0.69/0.88  cnf(c_0_70, plain, (X1=k3_tarski(k1_xboole_0)|r2_hidden(esk7_2(k3_tarski(k1_xboole_0),X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_23]), c_0_33])).
% 0.69/0.88  cnf(c_0_71, negated_conjecture, (~r2_hidden(X1,esk10_0)|~r2_hidden(X2,esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.69/0.88  cnf(c_0_72, plain, (X1=k1_xboole_0|r2_hidden(esk7_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_59]), c_0_59])).
% 0.69/0.88  cnf(c_0_73, negated_conjecture, (~r2_hidden(X1,esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_64])).
% 0.69/0.88  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_72]), c_0_65]), ['proof']).
% 0.69/0.88  # SZS output end CNFRefutation
% 0.69/0.88  # Proof object total steps             : 75
% 0.69/0.88  # Proof object clause steps            : 62
% 0.69/0.88  # Proof object formula steps           : 13
% 0.69/0.88  # Proof object conjectures             : 14
% 0.69/0.88  # Proof object clause conjectures      : 11
% 0.69/0.88  # Proof object formula conjectures     : 3
% 0.69/0.88  # Proof object initial clauses used    : 11
% 0.69/0.88  # Proof object initial formulas used   : 6
% 0.69/0.88  # Proof object generating inferences   : 43
% 0.69/0.88  # Proof object simplifying inferences  : 27
% 0.69/0.88  # Training examples: 0 positive, 0 negative
% 0.69/0.88  # Parsed axioms                        : 6
% 0.69/0.88  # Removed by relevancy pruning/SinE    : 0
% 0.69/0.88  # Initial clauses                      : 21
% 0.69/0.88  # Removed in clause preprocessing      : 1
% 0.69/0.88  # Initial clauses in saturation        : 20
% 0.69/0.88  # Processed clauses                    : 6050
% 0.69/0.88  # ...of these trivial                  : 61
% 0.69/0.88  # ...subsumed                          : 4987
% 0.69/0.88  # ...remaining for further processing  : 1002
% 0.69/0.88  # Other redundant clauses eliminated   : 1
% 0.69/0.88  # Clauses deleted for lack of memory   : 0
% 0.69/0.88  # Backward-subsumed                    : 32
% 0.69/0.88  # Backward-rewritten                   : 595
% 0.69/0.88  # Generated clauses                    : 48671
% 0.69/0.88  # ...of the previous two non-trivial   : 45447
% 0.69/0.88  # Contextual simplify-reflections      : 1
% 0.69/0.88  # Paramodulations                      : 48370
% 0.69/0.88  # Factorizations                       : 0
% 0.69/0.88  # Equation resolutions                 : 300
% 0.69/0.88  # Propositional unsat checks           : 0
% 0.69/0.88  #    Propositional check models        : 0
% 0.69/0.88  #    Propositional check unsatisfiable : 0
% 0.69/0.88  #    Propositional clauses             : 0
% 0.69/0.88  #    Propositional clauses after purity: 0
% 0.69/0.88  #    Propositional unsat core size     : 0
% 0.69/0.88  #    Propositional preprocessing time  : 0.000
% 0.69/0.88  #    Propositional encoding time       : 0.000
% 0.69/0.88  #    Propositional solver time         : 0.000
% 0.69/0.88  #    Success case prop preproc time    : 0.000
% 0.69/0.88  #    Success case prop encoding time   : 0.000
% 0.69/0.88  #    Success case prop solver time     : 0.000
% 0.69/0.88  # Current number of processed clauses  : 354
% 0.69/0.88  #    Positive orientable unit clauses  : 5
% 0.69/0.88  #    Positive unorientable unit clauses: 0
% 0.69/0.88  #    Negative unit clauses             : 4
% 0.69/0.88  #    Non-unit-clauses                  : 345
% 0.69/0.88  # Current number of unprocessed clauses: 36910
% 0.69/0.88  # ...number of literals in the above   : 169622
% 0.69/0.88  # Current number of archived formulas  : 0
% 0.69/0.88  # Current number of archived clauses   : 649
% 0.69/0.88  # Clause-clause subsumption calls (NU) : 67324
% 0.69/0.88  # Rec. Clause-clause subsumption calls : 29596
% 0.69/0.88  # Non-unit clause-clause subsumptions  : 3519
% 0.69/0.88  # Unit Clause-clause subsumption calls : 1738
% 0.69/0.88  # Rewrite failures with RHS unbound    : 0
% 0.69/0.88  # BW rewrite match attempts            : 17
% 0.69/0.88  # BW rewrite match successes           : 17
% 0.69/0.88  # Condensation attempts                : 0
% 0.69/0.88  # Condensation successes               : 0
% 0.69/0.88  # Termbank termtop insertions          : 468328
% 0.69/0.88  
% 0.69/0.88  # -------------------------------------------------
% 0.69/0.88  # User time                : 0.518 s
% 0.69/0.88  # System time              : 0.020 s
% 0.69/0.88  # Total time               : 0.538 s
% 0.69/0.88  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
