%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:07 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 163 expanded)
%              Number of clauses        :   35 (  72 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  185 ( 418 expanded)
%              Number of equality atoms :   61 ( 173 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t15_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & r2_hidden(k2_mcart_1(X1),X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t144_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t12_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
     => ( k1_mcart_1(X1) = X2
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))
       => ( ( k1_mcart_1(X1) = X2
            | k1_mcart_1(X1) = X3 )
          & r2_hidden(k2_mcart_1(X1),X4) ) ) ),
    inference(assume_negation,[status(cth)],[t15_mcart_1])).

fof(c_0_13,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_14,plain,(
    ! [X41,X42,X43] :
      ( r2_hidden(X41,X43)
      | r2_hidden(X42,X43)
      | X43 = k4_xboole_0(X43,k2_tarski(X41,X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).

fof(c_0_15,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,negated_conjecture,
    ( r2_hidden(esk7_0,k2_zfmisc_1(k2_tarski(esk8_0,esk9_0),esk10_0))
    & ( k1_mcart_1(esk7_0) != esk8_0
      | ~ r2_hidden(k2_mcart_1(esk7_0),esk10_0) )
    & ( k1_mcart_1(esk7_0) != esk9_0
      | ~ r2_hidden(k2_mcart_1(esk7_0),esk10_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | X2 = k4_xboole_0(X2,k2_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X47,X48,X49] :
      ( ( r2_hidden(k1_mcart_1(X47),X48)
        | ~ r2_hidden(X47,k2_zfmisc_1(X48,X49)) )
      & ( r2_hidden(k2_mcart_1(X47),X49)
        | ~ r2_hidden(X47,k2_zfmisc_1(X48,X49)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk7_0,k2_zfmisc_1(k2_tarski(esk8_0,esk9_0),esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X44,X45,X46] :
      ( ( r2_hidden(X44,X46)
        | ~ r1_tarski(k2_tarski(X44,X45),X46) )
      & ( r2_hidden(X45,X46)
        | ~ r1_tarski(k2_tarski(X44,X45),X46) )
      & ( ~ r2_hidden(X44,X46)
        | ~ r2_hidden(X45,X46)
        | r1_tarski(k2_tarski(X44,X45),X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_25,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_26,plain,(
    ! [X24,X25,X26,X27,X30,X31,X32,X33,X34,X35,X37,X38] :
      ( ( r2_hidden(esk2_4(X24,X25,X26,X27),X24)
        | ~ r2_hidden(X27,X26)
        | X26 != k2_zfmisc_1(X24,X25) )
      & ( r2_hidden(esk3_4(X24,X25,X26,X27),X25)
        | ~ r2_hidden(X27,X26)
        | X26 != k2_zfmisc_1(X24,X25) )
      & ( X27 = k4_tarski(esk2_4(X24,X25,X26,X27),esk3_4(X24,X25,X26,X27))
        | ~ r2_hidden(X27,X26)
        | X26 != k2_zfmisc_1(X24,X25) )
      & ( ~ r2_hidden(X31,X24)
        | ~ r2_hidden(X32,X25)
        | X30 != k4_tarski(X31,X32)
        | r2_hidden(X30,X26)
        | X26 != k2_zfmisc_1(X24,X25) )
      & ( ~ r2_hidden(esk4_3(X33,X34,X35),X35)
        | ~ r2_hidden(X37,X33)
        | ~ r2_hidden(X38,X34)
        | esk4_3(X33,X34,X35) != k4_tarski(X37,X38)
        | X35 = k2_zfmisc_1(X33,X34) )
      & ( r2_hidden(esk5_3(X33,X34,X35),X33)
        | r2_hidden(esk4_3(X33,X34,X35),X35)
        | X35 = k2_zfmisc_1(X33,X34) )
      & ( r2_hidden(esk6_3(X33,X34,X35),X34)
        | r2_hidden(esk4_3(X33,X34,X35),X35)
        | X35 = k2_zfmisc_1(X33,X34) )
      & ( esk4_3(X33,X34,X35) = k4_tarski(esk5_3(X33,X34,X35),esk6_3(X33,X34,X35))
        | r2_hidden(esk4_3(X33,X34,X35),X35)
        | X35 = k2_zfmisc_1(X33,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( X2 = k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X3))
    | r2_hidden(X3,X2)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk7_0,k2_zfmisc_1(k2_enumset1(esk8_0,esk8_0,esk8_0,esk9_0),esk10_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_20]),c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X4,k2_enumset1(X1,X1,X1,X3))
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_20]),c_0_21])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X50,X51,X52] :
      ( ( k1_mcart_1(X50) = X51
        | ~ r2_hidden(X50,k2_zfmisc_1(k1_tarski(X51),X52)) )
      & ( r2_hidden(k2_mcart_1(X50),X52)
        | ~ r2_hidden(X50,k2_zfmisc_1(k1_tarski(X51),X52)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).

fof(c_0_40,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk7_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk9_0,X1)
    | r2_hidden(esk8_0,X1)
    | ~ r2_hidden(k1_mcart_1(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k2_mcart_1(esk7_0)),k2_zfmisc_1(X2,esk10_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk8_0,k2_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),X1))
    | r2_hidden(esk9_0,k2_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_49,plain,(
    ! [X53,X54] :
      ( k1_mcart_1(k4_tarski(X53,X54)) = X53
      & k2_mcart_1(k4_tarski(X53,X54)) = X54 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_50,negated_conjecture,
    ( k1_mcart_1(esk7_0) != esk9_0
    | ~ r2_hidden(k2_mcart_1(esk7_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_51,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_20]),c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,k2_mcart_1(esk7_0)),k2_zfmisc_1(k2_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),X1),esk10_0))
    | r2_hidden(esk8_0,k2_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k1_mcart_1(esk7_0) != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_42])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk8_0,k2_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_56,negated_conjecture,
    ( k1_mcart_1(esk7_0) != esk8_0
    | ~ r2_hidden(k2_mcart_1(esk7_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,k2_mcart_1(esk7_0)),k2_zfmisc_1(k2_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0)),esk10_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( k1_mcart_1(esk7_0) != esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_42])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_57]),c_0_53]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:19:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.66  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.47/0.66  # and selection function SelectNegativeLiterals.
% 0.47/0.66  #
% 0.47/0.66  # Preprocessing time       : 0.028 s
% 0.47/0.66  # Presaturation interreduction done
% 0.47/0.66  
% 0.47/0.66  # Proof found!
% 0.47/0.66  # SZS status Theorem
% 0.47/0.66  # SZS output start CNFRefutation
% 0.47/0.66  fof(t15_mcart_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&r2_hidden(k2_mcart_1(X1),X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 0.47/0.66  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.47/0.66  fof(t144_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 0.47/0.66  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.47/0.66  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.47/0.66  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.47/0.66  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.47/0.66  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.47/0.66  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.47/0.66  fof(t12_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 0.47/0.66  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.47/0.66  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.47/0.66  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&r2_hidden(k2_mcart_1(X1),X4)))), inference(assume_negation,[status(cth)],[t15_mcart_1])).
% 0.47/0.66  fof(c_0_13, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.47/0.66  fof(c_0_14, plain, ![X41, X42, X43]:(r2_hidden(X41,X43)|r2_hidden(X42,X43)|X43=k4_xboole_0(X43,k2_tarski(X41,X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).
% 0.47/0.66  fof(c_0_15, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.47/0.66  fof(c_0_16, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.47/0.66  fof(c_0_17, negated_conjecture, (r2_hidden(esk7_0,k2_zfmisc_1(k2_tarski(esk8_0,esk9_0),esk10_0))&((k1_mcart_1(esk7_0)!=esk8_0|~r2_hidden(k2_mcart_1(esk7_0),esk10_0))&(k1_mcart_1(esk7_0)!=esk9_0|~r2_hidden(k2_mcart_1(esk7_0),esk10_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.47/0.66  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.66  cnf(c_0_19, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|X2=k4_xboole_0(X2,k2_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.66  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.47/0.66  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.47/0.66  fof(c_0_22, plain, ![X47, X48, X49]:((r2_hidden(k1_mcart_1(X47),X48)|~r2_hidden(X47,k2_zfmisc_1(X48,X49)))&(r2_hidden(k2_mcart_1(X47),X49)|~r2_hidden(X47,k2_zfmisc_1(X48,X49)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.47/0.66  cnf(c_0_23, negated_conjecture, (r2_hidden(esk7_0,k2_zfmisc_1(k2_tarski(esk8_0,esk9_0),esk10_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.66  fof(c_0_24, plain, ![X44, X45, X46]:(((r2_hidden(X44,X46)|~r1_tarski(k2_tarski(X44,X45),X46))&(r2_hidden(X45,X46)|~r1_tarski(k2_tarski(X44,X45),X46)))&(~r2_hidden(X44,X46)|~r2_hidden(X45,X46)|r1_tarski(k2_tarski(X44,X45),X46))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.47/0.66  fof(c_0_25, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.47/0.66  fof(c_0_26, plain, ![X24, X25, X26, X27, X30, X31, X32, X33, X34, X35, X37, X38]:(((((r2_hidden(esk2_4(X24,X25,X26,X27),X24)|~r2_hidden(X27,X26)|X26!=k2_zfmisc_1(X24,X25))&(r2_hidden(esk3_4(X24,X25,X26,X27),X25)|~r2_hidden(X27,X26)|X26!=k2_zfmisc_1(X24,X25)))&(X27=k4_tarski(esk2_4(X24,X25,X26,X27),esk3_4(X24,X25,X26,X27))|~r2_hidden(X27,X26)|X26!=k2_zfmisc_1(X24,X25)))&(~r2_hidden(X31,X24)|~r2_hidden(X32,X25)|X30!=k4_tarski(X31,X32)|r2_hidden(X30,X26)|X26!=k2_zfmisc_1(X24,X25)))&((~r2_hidden(esk4_3(X33,X34,X35),X35)|(~r2_hidden(X37,X33)|~r2_hidden(X38,X34)|esk4_3(X33,X34,X35)!=k4_tarski(X37,X38))|X35=k2_zfmisc_1(X33,X34))&(((r2_hidden(esk5_3(X33,X34,X35),X33)|r2_hidden(esk4_3(X33,X34,X35),X35)|X35=k2_zfmisc_1(X33,X34))&(r2_hidden(esk6_3(X33,X34,X35),X34)|r2_hidden(esk4_3(X33,X34,X35),X35)|X35=k2_zfmisc_1(X33,X34)))&(esk4_3(X33,X34,X35)=k4_tarski(esk5_3(X33,X34,X35),esk6_3(X33,X34,X35))|r2_hidden(esk4_3(X33,X34,X35),X35)|X35=k2_zfmisc_1(X33,X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.47/0.66  cnf(c_0_27, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_18])).
% 0.47/0.66  cnf(c_0_28, plain, (X2=k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X3))|r2_hidden(X3,X2)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.47/0.66  cnf(c_0_29, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.47/0.66  cnf(c_0_30, negated_conjecture, (r2_hidden(esk7_0,k2_zfmisc_1(k2_enumset1(esk8_0,esk8_0,esk8_0,esk9_0),esk10_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_20]), c_0_21])).
% 0.47/0.66  cnf(c_0_31, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.66  cnf(c_0_32, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.47/0.66  cnf(c_0_33, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.66  cnf(c_0_34, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.47/0.66  cnf(c_0_35, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|~r2_hidden(X4,k2_enumset1(X1,X1,X1,X3))|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.47/0.66  cnf(c_0_36, negated_conjecture, (r2_hidden(k1_mcart_1(esk7_0),k2_enumset1(esk8_0,esk8_0,esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.47/0.66  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_20]), c_0_21])).
% 0.47/0.66  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_32])).
% 0.47/0.66  fof(c_0_39, plain, ![X50, X51, X52]:((k1_mcart_1(X50)=X51|~r2_hidden(X50,k2_zfmisc_1(k1_tarski(X51),X52)))&(r2_hidden(k2_mcart_1(X50),X52)|~r2_hidden(X50,k2_zfmisc_1(k1_tarski(X51),X52)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).
% 0.47/0.66  fof(c_0_40, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.47/0.66  cnf(c_0_41, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).
% 0.47/0.66  cnf(c_0_42, negated_conjecture, (r2_hidden(k2_mcart_1(esk7_0),esk10_0)), inference(spm,[status(thm)],[c_0_34, c_0_30])).
% 0.47/0.66  cnf(c_0_43, negated_conjecture, (r2_hidden(esk9_0,X1)|r2_hidden(esk8_0,X1)|~r2_hidden(k1_mcart_1(esk7_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.47/0.66  cnf(c_0_44, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.47/0.66  cnf(c_0_45, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.47/0.66  cnf(c_0_46, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.47/0.66  cnf(c_0_47, negated_conjecture, (r2_hidden(k4_tarski(X1,k2_mcart_1(esk7_0)),k2_zfmisc_1(X2,esk10_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.47/0.66  cnf(c_0_48, negated_conjecture, (r2_hidden(esk8_0,k2_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),X1))|r2_hidden(esk9_0,k2_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.47/0.66  fof(c_0_49, plain, ![X53, X54]:(k1_mcart_1(k4_tarski(X53,X54))=X53&k2_mcart_1(k4_tarski(X53,X54))=X54), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.47/0.66  cnf(c_0_50, negated_conjecture, (k1_mcart_1(esk7_0)!=esk9_0|~r2_hidden(k2_mcart_1(esk7_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.66  cnf(c_0_51, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_20]), c_0_21])).
% 0.47/0.66  cnf(c_0_52, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,k2_mcart_1(esk7_0)),k2_zfmisc_1(k2_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),X1),esk10_0))|r2_hidden(esk8_0,k2_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.47/0.66  cnf(c_0_53, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.47/0.66  cnf(c_0_54, negated_conjecture, (k1_mcart_1(esk7_0)!=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_42])])).
% 0.47/0.66  cnf(c_0_55, negated_conjecture, (r2_hidden(esk8_0,k2_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0)))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])).
% 0.47/0.66  cnf(c_0_56, negated_conjecture, (k1_mcart_1(esk7_0)!=esk8_0|~r2_hidden(k2_mcart_1(esk7_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.66  cnf(c_0_57, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,k2_mcart_1(esk7_0)),k2_zfmisc_1(k2_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0)),esk10_0))), inference(spm,[status(thm)],[c_0_47, c_0_55])).
% 0.47/0.66  cnf(c_0_58, negated_conjecture, (k1_mcart_1(esk7_0)!=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_42])])).
% 0.47/0.66  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_57]), c_0_53]), c_0_58]), ['proof']).
% 0.47/0.66  # SZS output end CNFRefutation
% 0.47/0.66  # Proof object total steps             : 60
% 0.47/0.66  # Proof object clause steps            : 35
% 0.47/0.66  # Proof object formula steps           : 25
% 0.47/0.66  # Proof object conjectures             : 18
% 0.47/0.66  # Proof object clause conjectures      : 15
% 0.47/0.66  # Proof object formula conjectures     : 3
% 0.47/0.66  # Proof object initial clauses used    : 15
% 0.47/0.66  # Proof object initial formulas used   : 12
% 0.47/0.66  # Proof object generating inferences   : 11
% 0.47/0.66  # Proof object simplifying inferences  : 21
% 0.47/0.66  # Training examples: 0 positive, 0 negative
% 0.47/0.66  # Parsed axioms                        : 12
% 0.47/0.66  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.66  # Initial clauses                      : 33
% 0.47/0.66  # Removed in clause preprocessing      : 3
% 0.47/0.66  # Initial clauses in saturation        : 30
% 0.47/0.66  # Processed clauses                    : 465
% 0.47/0.66  # ...of these trivial                  : 18
% 0.47/0.66  # ...subsumed                          : 44
% 0.47/0.66  # ...remaining for further processing  : 403
% 0.47/0.66  # Other redundant clauses eliminated   : 72
% 0.47/0.66  # Clauses deleted for lack of memory   : 0
% 0.47/0.66  # Backward-subsumed                    : 1
% 0.47/0.66  # Backward-rewritten                   : 3
% 0.47/0.66  # Generated clauses                    : 25726
% 0.47/0.66  # ...of the previous two non-trivial   : 25149
% 0.47/0.66  # Contextual simplify-reflections      : 0
% 0.47/0.66  # Paramodulations                      : 25649
% 0.47/0.66  # Factorizations                       : 6
% 0.47/0.66  # Equation resolutions                 : 72
% 0.47/0.66  # Propositional unsat checks           : 0
% 0.47/0.66  #    Propositional check models        : 0
% 0.47/0.66  #    Propositional check unsatisfiable : 0
% 0.47/0.66  #    Propositional clauses             : 0
% 0.47/0.66  #    Propositional clauses after purity: 0
% 0.47/0.66  #    Propositional unsat core size     : 0
% 0.47/0.66  #    Propositional preprocessing time  : 0.000
% 0.47/0.66  #    Propositional encoding time       : 0.000
% 0.47/0.66  #    Propositional solver time         : 0.000
% 0.47/0.66  #    Success case prop preproc time    : 0.000
% 0.47/0.66  #    Success case prop encoding time   : 0.000
% 0.47/0.66  #    Success case prop solver time     : 0.000
% 0.47/0.66  # Current number of processed clauses  : 362
% 0.47/0.66  #    Positive orientable unit clauses  : 146
% 0.47/0.66  #    Positive unorientable unit clauses: 0
% 0.47/0.66  #    Negative unit clauses             : 2
% 0.47/0.66  #    Non-unit-clauses                  : 214
% 0.47/0.66  # Current number of unprocessed clauses: 24658
% 0.47/0.66  # ...number of literals in the above   : 78176
% 0.47/0.66  # Current number of archived formulas  : 0
% 0.47/0.66  # Current number of archived clauses   : 35
% 0.47/0.66  # Clause-clause subsumption calls (NU) : 3148
% 0.47/0.66  # Rec. Clause-clause subsumption calls : 2599
% 0.47/0.66  # Non-unit clause-clause subsumptions  : 45
% 0.47/0.66  # Unit Clause-clause subsumption calls : 167
% 0.47/0.66  # Rewrite failures with RHS unbound    : 0
% 0.47/0.66  # BW rewrite match attempts            : 363
% 0.47/0.66  # BW rewrite match successes           : 2
% 0.47/0.66  # Condensation attempts                : 0
% 0.47/0.66  # Condensation successes               : 0
% 0.47/0.66  # Termbank termtop insertions          : 761326
% 0.47/0.66  
% 0.47/0.66  # -------------------------------------------------
% 0.47/0.66  # User time                : 0.310 s
% 0.47/0.66  # System time              : 0.020 s
% 0.47/0.66  # Total time               : 0.330 s
% 0.47/0.66  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
