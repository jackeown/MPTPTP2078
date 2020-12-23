%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:04 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   84 (1003 expanded)
%              Number of clauses        :   65 ( 483 expanded)
%              Number of leaves         :    9 ( 244 expanded)
%              Depth                    :   20
%              Number of atoms          :  248 (4107 expanded)
%              Number of equality atoms :   69 (1531 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t6_xboole_0,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r2_hidden(X15,X16)
        | ~ r2_hidden(X15,X17)
        | ~ r2_hidden(X15,k5_xboole_0(X16,X17)) )
      & ( r2_hidden(X15,X16)
        | r2_hidden(X15,X17)
        | ~ r2_hidden(X15,k5_xboole_0(X16,X17)) )
      & ( ~ r2_hidden(X15,X16)
        | r2_hidden(X15,X17)
        | r2_hidden(X15,k5_xboole_0(X16,X17)) )
      & ( ~ r2_hidden(X15,X17)
        | r2_hidden(X15,X16)
        | r2_hidden(X15,k5_xboole_0(X16,X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

fof(c_0_11,plain,(
    ! [X21] : k5_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_12,plain,(
    ! [X39,X40,X41,X42] :
      ( ( r2_hidden(X39,X41)
        | ~ r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)) )
      & ( r2_hidden(X40,X42)
        | ~ r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)) )
      & ( ~ r2_hidden(X39,X41)
        | ~ r2_hidden(X40,X42)
        | r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_13,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k2_zfmisc_1(esk10_0,esk11_0)
    & esk8_0 != k1_xboole_0
    & esk9_0 != k1_xboole_0
    & ( esk8_0 != esk10_0
      | esk9_0 != esk11_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k2_zfmisc_1(esk10_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X22,X23,X24,X25,X28,X29,X30,X31,X32,X33,X35,X36] :
      ( ( r2_hidden(esk3_4(X22,X23,X24,X25),X22)
        | ~ r2_hidden(X25,X24)
        | X24 != k2_zfmisc_1(X22,X23) )
      & ( r2_hidden(esk4_4(X22,X23,X24,X25),X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k2_zfmisc_1(X22,X23) )
      & ( X25 = k4_tarski(esk3_4(X22,X23,X24,X25),esk4_4(X22,X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k2_zfmisc_1(X22,X23) )
      & ( ~ r2_hidden(X29,X22)
        | ~ r2_hidden(X30,X23)
        | X28 != k4_tarski(X29,X30)
        | r2_hidden(X28,X24)
        | X24 != k2_zfmisc_1(X22,X23) )
      & ( ~ r2_hidden(esk5_3(X31,X32,X33),X33)
        | ~ r2_hidden(X35,X31)
        | ~ r2_hidden(X36,X32)
        | esk5_3(X31,X32,X33) != k4_tarski(X35,X36)
        | X33 = k2_zfmisc_1(X31,X32) )
      & ( r2_hidden(esk6_3(X31,X32,X33),X31)
        | r2_hidden(esk5_3(X31,X32,X33),X33)
        | X33 = k2_zfmisc_1(X31,X32) )
      & ( r2_hidden(esk7_3(X31,X32,X33),X32)
        | r2_hidden(esk5_3(X31,X32,X33),X33)
        | X33 = k2_zfmisc_1(X31,X32) )
      & ( esk5_3(X31,X32,X33) = k4_tarski(esk6_3(X31,X32,X33),esk7_3(X31,X32,X33))
        | r2_hidden(esk5_3(X31,X32,X33),X33)
        | X33 = k2_zfmisc_1(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_22,plain,(
    ! [X43,X44] :
      ( ( k2_zfmisc_1(X43,X44) != k1_xboole_0
        | X43 = k1_xboole_0
        | X44 = k1_xboole_0 )
      & ( X43 != k1_xboole_0
        | k2_zfmisc_1(X43,X44) = k1_xboole_0 )
      & ( X44 != k1_xboole_0
        | k2_zfmisc_1(X43,X44) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,esk10_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_25,plain,(
    ! [X18,X19] :
      ( ( r2_hidden(esk2_2(X18,X19),X19)
        | ~ r2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_2(X18,X19),X18)
        | ~ r2_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).

fof(c_0_26,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | ~ r2_xboole_0(X13,X14) )
      & ( X13 != X14
        | ~ r2_xboole_0(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | X13 = X14
        | r2_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r2_hidden(esk1_2(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,esk10_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_20])).

cnf(c_0_34,plain,
    ( r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk10_0)
    | ~ r2_xboole_0(X2,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k1_xboole_0 = X1
    | r2_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(esk3_4(k1_xboole_0,X1,k1_xboole_0,X2),X3)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_34]),c_0_35]),c_0_35])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,esk10_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,esk11_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_18])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_40])).

cnf(c_0_45,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(X1,esk10_0)
    | ~ r2_hidden(esk1_2(X1,esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,esk11_0)
    | ~ r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_24])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_35])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_2(X1,X2),X3)
    | ~ r2_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk8_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_20])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,X1),esk11_0)
    | r1_tarski(esk9_0,X1)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk5_3(k1_xboole_0,X1,esk9_0),esk11_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_38])).

cnf(c_0_55,plain,
    ( r2_hidden(esk2_2(X1,X2),X3)
    | ~ r2_xboole_0(X1,X2)
    | ~ r1_tarski(X4,X3)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_46,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( esk10_0 = esk8_0
    | r2_xboole_0(esk8_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,X1),esk11_0)
    | r1_tarski(esk9_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_49]),c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk8_0,esk9_0))
    | ~ r2_hidden(X2,esk11_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk5_3(k1_xboole_0,X1,esk9_0),esk11_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_49]),c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( esk10_0 = esk8_0
    | r2_hidden(esk2_2(esk8_0,esk10_0),X1)
    | ~ r1_tarski(esk10_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk9_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X2,esk11_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk5_3(k1_xboole_0,X1,esk9_0),X2)
    | ~ r1_tarski(esk11_0,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( esk10_0 = esk8_0
    | r2_hidden(esk2_2(esk8_0,esk10_0),X1)
    | ~ r1_tarski(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( esk11_0 = esk9_0
    | r2_xboole_0(esk9_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_61])])).

cnf(c_0_68,negated_conjecture,
    ( esk10_0 = esk8_0
    | r2_hidden(esk2_2(esk8_0,esk10_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( esk11_0 = esk9_0
    | r2_hidden(esk2_2(esk9_0,esk11_0),X1)
    | ~ r1_tarski(esk11_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_66])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(esk2_2(X1,X2),X1)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_71,negated_conjecture,
    ( esk10_0 = esk8_0
    | r2_hidden(esk2_2(esk8_0,esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( esk11_0 = esk9_0
    | r2_hidden(esk2_2(esk9_0,esk11_0),X1)
    | ~ r1_tarski(esk11_0,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_61])).

cnf(c_0_73,negated_conjecture,
    ( esk8_0 != esk10_0
    | esk9_0 != esk11_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_74,negated_conjecture,
    ( esk10_0 = esk8_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_56])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk11_0)
    | ~ r2_hidden(X2,esk10_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_58])).

cnf(c_0_76,negated_conjecture,
    ( esk11_0 = esk9_0
    | r2_hidden(esk2_2(esk9_0,esk11_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_61])).

cnf(c_0_77,negated_conjecture,
    ( esk11_0 != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk11_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(rw,[status(thm)],[c_0_75,c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk2_2(esk9_0,esk11_0),esk11_0) ),
    inference(sr,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk2_2(esk9_0,esk11_0),esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk2_2(esk9_0,esk11_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_49]),c_0_53])).

cnf(c_0_82,negated_conjecture,
    ( r2_xboole_0(esk9_0,esk11_0) ),
    inference(sr,[status(thm)],[c_0_66,c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_81]),c_0_82])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:10:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.021 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.19/0.37  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.19/0.37  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.37  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.37  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.19/0.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.37  fof(t6_xboole_0, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&![X3]:~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 0.19/0.37  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.19/0.37  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 0.19/0.37  fof(c_0_10, plain, ![X15, X16, X17]:(((~r2_hidden(X15,X16)|~r2_hidden(X15,X17)|~r2_hidden(X15,k5_xboole_0(X16,X17)))&(r2_hidden(X15,X16)|r2_hidden(X15,X17)|~r2_hidden(X15,k5_xboole_0(X16,X17))))&((~r2_hidden(X15,X16)|r2_hidden(X15,X17)|r2_hidden(X15,k5_xboole_0(X16,X17)))&(~r2_hidden(X15,X17)|r2_hidden(X15,X16)|r2_hidden(X15,k5_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.19/0.37  fof(c_0_11, plain, ![X21]:k5_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.37  fof(c_0_12, plain, ![X39, X40, X41, X42]:(((r2_hidden(X39,X41)|~r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)))&(r2_hidden(X40,X42)|~r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42))))&(~r2_hidden(X39,X41)|~r2_hidden(X40,X42)|r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.37  fof(c_0_13, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k2_zfmisc_1(esk10_0,esk11_0)&((esk8_0!=k1_xboole_0&esk9_0!=k1_xboole_0)&(esk8_0!=esk10_0|esk9_0!=esk11_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.37  cnf(c_0_14, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_15, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  fof(c_0_16, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.37  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k2_zfmisc_1(esk10_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_19, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.37  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  fof(c_0_21, plain, ![X22, X23, X24, X25, X28, X29, X30, X31, X32, X33, X35, X36]:(((((r2_hidden(esk3_4(X22,X23,X24,X25),X22)|~r2_hidden(X25,X24)|X24!=k2_zfmisc_1(X22,X23))&(r2_hidden(esk4_4(X22,X23,X24,X25),X23)|~r2_hidden(X25,X24)|X24!=k2_zfmisc_1(X22,X23)))&(X25=k4_tarski(esk3_4(X22,X23,X24,X25),esk4_4(X22,X23,X24,X25))|~r2_hidden(X25,X24)|X24!=k2_zfmisc_1(X22,X23)))&(~r2_hidden(X29,X22)|~r2_hidden(X30,X23)|X28!=k4_tarski(X29,X30)|r2_hidden(X28,X24)|X24!=k2_zfmisc_1(X22,X23)))&((~r2_hidden(esk5_3(X31,X32,X33),X33)|(~r2_hidden(X35,X31)|~r2_hidden(X36,X32)|esk5_3(X31,X32,X33)!=k4_tarski(X35,X36))|X33=k2_zfmisc_1(X31,X32))&(((r2_hidden(esk6_3(X31,X32,X33),X31)|r2_hidden(esk5_3(X31,X32,X33),X33)|X33=k2_zfmisc_1(X31,X32))&(r2_hidden(esk7_3(X31,X32,X33),X32)|r2_hidden(esk5_3(X31,X32,X33),X33)|X33=k2_zfmisc_1(X31,X32)))&(esk5_3(X31,X32,X33)=k4_tarski(esk6_3(X31,X32,X33),esk7_3(X31,X32,X33))|r2_hidden(esk5_3(X31,X32,X33),X33)|X33=k2_zfmisc_1(X31,X32))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.19/0.37  fof(c_0_22, plain, ![X43, X44]:((k2_zfmisc_1(X43,X44)!=k1_xboole_0|(X43=k1_xboole_0|X44=k1_xboole_0))&((X43!=k1_xboole_0|k2_zfmisc_1(X43,X44)=k1_xboole_0)&(X44!=k1_xboole_0|k2_zfmisc_1(X43,X44)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,esk10_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.37  cnf(c_0_24, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  fof(c_0_25, plain, ![X18, X19]:((r2_hidden(esk2_2(X18,X19),X19)|~r2_xboole_0(X18,X19))&(~r2_hidden(esk2_2(X18,X19),X18)|~r2_xboole_0(X18,X19))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).
% 0.19/0.37  fof(c_0_26, plain, ![X13, X14]:(((r1_tarski(X13,X14)|~r2_xboole_0(X13,X14))&(X13!=X14|~r2_xboole_0(X13,X14)))&(~r1_tarski(X13,X14)|X13=X14|r2_xboole_0(X13,X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.19/0.37  cnf(c_0_27, plain, (r1_tarski(k1_xboole_0,X1)|~r2_hidden(esk1_2(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.37  cnf(c_0_28, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_29, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,esk10_0)|~r2_hidden(X2,esk9_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.37  cnf(c_0_31, plain, (r2_hidden(esk2_2(X1,X2),X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_32, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_33, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_20])).
% 0.19/0.37  cnf(c_0_34, plain, (r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_35, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_29])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,esk10_0)|~r2_xboole_0(X2,esk9_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.37  cnf(c_0_37, plain, (k1_xboole_0=X1|r2_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_40, plain, (~r2_hidden(esk3_4(k1_xboole_0,X1,k1_xboole_0,X2),X3)|~r2_hidden(X2,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_34]), c_0_35]), c_0_35])).
% 0.19/0.37  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,esk10_0)|~r2_hidden(X1,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,esk11_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_39, c_0_18])).
% 0.19/0.37  cnf(c_0_44, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_40])).
% 0.19/0.37  cnf(c_0_45, plain, (r2_hidden(esk6_3(X1,X2,X3),X1)|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_46, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (r1_tarski(X1,esk10_0)|~r2_hidden(esk1_2(X1,esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (r2_hidden(X1,esk11_0)|~r2_hidden(X1,esk9_0)|~r2_hidden(X2,esk8_0)), inference(spm,[status(thm)],[c_0_43, c_0_24])).
% 0.19/0.37  cnf(c_0_49, plain, (X1=k1_xboole_0|r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_35])).
% 0.19/0.37  cnf(c_0_50, plain, (r2_hidden(esk2_2(X1,X2),X3)|~r2_xboole_0(X1,X2)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_46, c_0_31])).
% 0.19/0.37  cnf(c_0_51, negated_conjecture, (r1_tarski(esk8_0,esk10_0)), inference(spm,[status(thm)],[c_0_47, c_0_20])).
% 0.19/0.37  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_2(esk9_0,X1),esk11_0)|r1_tarski(esk9_0,X1)|~r2_hidden(X2,esk8_0)), inference(spm,[status(thm)],[c_0_48, c_0_20])).
% 0.19/0.37  cnf(c_0_53, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_54, negated_conjecture, (r2_hidden(esk5_3(k1_xboole_0,X1,esk9_0),esk11_0)|~r2_hidden(X2,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_38])).
% 0.19/0.37  cnf(c_0_55, plain, (r2_hidden(esk2_2(X1,X2),X3)|~r2_xboole_0(X1,X2)|~r1_tarski(X4,X3)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_46, c_0_50])).
% 0.19/0.37  cnf(c_0_56, negated_conjecture, (esk10_0=esk8_0|r2_xboole_0(esk8_0,esk10_0)), inference(spm,[status(thm)],[c_0_32, c_0_51])).
% 0.19/0.37  cnf(c_0_57, negated_conjecture, (r2_hidden(esk1_2(esk9_0,X1),esk11_0)|r1_tarski(esk9_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_49]), c_0_53])).
% 0.19/0.37  cnf(c_0_58, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk8_0,esk9_0))|~r2_hidden(X2,esk11_0)|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_24, c_0_18])).
% 0.19/0.37  cnf(c_0_59, negated_conjecture, (r2_hidden(esk5_3(k1_xboole_0,X1,esk9_0),esk11_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_49]), c_0_53])).
% 0.19/0.37  cnf(c_0_60, negated_conjecture, (esk10_0=esk8_0|r2_hidden(esk2_2(esk8_0,esk10_0),X1)|~r1_tarski(esk10_0,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.37  cnf(c_0_61, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_41, c_0_20])).
% 0.19/0.37  cnf(c_0_62, negated_conjecture, (r1_tarski(esk9_0,esk11_0)), inference(spm,[status(thm)],[c_0_41, c_0_57])).
% 0.19/0.37  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X2,esk11_0)|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_17, c_0_58])).
% 0.19/0.37  cnf(c_0_64, negated_conjecture, (r2_hidden(esk5_3(k1_xboole_0,X1,esk9_0),X2)|~r1_tarski(esk11_0,X2)), inference(spm,[status(thm)],[c_0_46, c_0_59])).
% 0.19/0.37  cnf(c_0_65, negated_conjecture, (esk10_0=esk8_0|r2_hidden(esk2_2(esk8_0,esk10_0),X1)|~r1_tarski(esk10_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.37  cnf(c_0_66, negated_conjecture, (esk11_0=esk9_0|r2_xboole_0(esk9_0,esk11_0)), inference(spm,[status(thm)],[c_0_32, c_0_62])).
% 0.19/0.37  cnf(c_0_67, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_61])])).
% 0.19/0.37  cnf(c_0_68, negated_conjecture, (esk10_0=esk8_0|r2_hidden(esk2_2(esk8_0,esk10_0),esk10_0)), inference(spm,[status(thm)],[c_0_65, c_0_61])).
% 0.19/0.37  cnf(c_0_69, negated_conjecture, (esk11_0=esk9_0|r2_hidden(esk2_2(esk9_0,esk11_0),X1)|~r1_tarski(esk11_0,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_55, c_0_66])).
% 0.19/0.37  cnf(c_0_70, plain, (~r2_hidden(esk2_2(X1,X2),X1)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_71, negated_conjecture, (esk10_0=esk8_0|r2_hidden(esk2_2(esk8_0,esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.37  cnf(c_0_72, negated_conjecture, (esk11_0=esk9_0|r2_hidden(esk2_2(esk9_0,esk11_0),X1)|~r1_tarski(esk11_0,X1)), inference(spm,[status(thm)],[c_0_69, c_0_61])).
% 0.19/0.37  cnf(c_0_73, negated_conjecture, (esk8_0!=esk10_0|esk9_0!=esk11_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_74, negated_conjecture, (esk10_0=esk8_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_56])).
% 0.19/0.37  cnf(c_0_75, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X1,esk11_0)|~r2_hidden(X2,esk10_0)), inference(spm,[status(thm)],[c_0_39, c_0_58])).
% 0.19/0.37  cnf(c_0_76, negated_conjecture, (esk11_0=esk9_0|r2_hidden(esk2_2(esk9_0,esk11_0),esk11_0)), inference(spm,[status(thm)],[c_0_72, c_0_61])).
% 0.19/0.37  cnf(c_0_77, negated_conjecture, (esk11_0!=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74])])).
% 0.19/0.37  cnf(c_0_78, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X1,esk11_0)|~r2_hidden(X2,esk8_0)), inference(rw,[status(thm)],[c_0_75, c_0_74])).
% 0.19/0.37  cnf(c_0_79, negated_conjecture, (r2_hidden(esk2_2(esk9_0,esk11_0),esk11_0)), inference(sr,[status(thm)],[c_0_76, c_0_77])).
% 0.19/0.37  cnf(c_0_80, negated_conjecture, (r2_hidden(esk2_2(esk9_0,esk11_0),esk9_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.19/0.37  cnf(c_0_81, negated_conjecture, (r2_hidden(esk2_2(esk9_0,esk11_0),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_49]), c_0_53])).
% 0.19/0.37  cnf(c_0_82, negated_conjecture, (r2_xboole_0(esk9_0,esk11_0)), inference(sr,[status(thm)],[c_0_66, c_0_77])).
% 0.19/0.37  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_81]), c_0_82])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 84
% 0.19/0.37  # Proof object clause steps            : 65
% 0.19/0.37  # Proof object formula steps           : 19
% 0.19/0.37  # Proof object conjectures             : 42
% 0.19/0.37  # Proof object clause conjectures      : 39
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 18
% 0.19/0.37  # Proof object initial formulas used   : 9
% 0.19/0.37  # Proof object generating inferences   : 41
% 0.19/0.37  # Proof object simplifying inferences  : 21
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 9
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 31
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 31
% 0.19/0.37  # Processed clauses                    : 266
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 73
% 0.19/0.37  # ...remaining for further processing  : 193
% 0.19/0.37  # Other redundant clauses eliminated   : 8
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 8
% 0.19/0.37  # Backward-rewritten                   : 45
% 0.19/0.37  # Generated clauses                    : 681
% 0.19/0.37  # ...of the previous two non-trivial   : 681
% 0.19/0.37  # Contextual simplify-reflections      : 2
% 0.19/0.37  # Paramodulations                      : 670
% 0.19/0.37  # Factorizations                       : 2
% 0.19/0.37  # Equation resolutions                 : 8
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 101
% 0.19/0.37  #    Positive orientable unit clauses  : 15
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 10
% 0.19/0.37  #    Non-unit-clauses                  : 76
% 0.19/0.37  # Current number of unprocessed clauses: 416
% 0.19/0.37  # ...number of literals in the above   : 1377
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 85
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 1972
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 1263
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 41
% 0.19/0.37  # Unit Clause-clause subsumption calls : 187
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 8
% 0.19/0.37  # BW rewrite match successes           : 7
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 11351
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.037 s
% 0.19/0.37  # System time              : 0.002 s
% 0.19/0.37  # Total time               : 0.039 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
