%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:51 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  101 (16476 expanded)
%              Number of clauses        :   66 (6530 expanded)
%              Number of leaves         :   17 (4898 expanded)
%              Depth                    :   18
%              Number of atoms          :  236 (25819 expanded)
%              Number of equality atoms :  124 (19140 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

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

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_17,plain,(
    ! [X66,X67] : k3_tarski(k2_tarski(X66,X67)) = k2_xboole_0(X66,X67) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X39,X40] : k1_enumset1(X39,X39,X40) = k2_tarski(X39,X40) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X29,X30] : r1_tarski(X29,k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_21,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X41,X42,X43] : k2_enumset1(X41,X41,X42,X43) = k1_enumset1(X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X44,X45,X46,X47] : k3_enumset1(X44,X44,X45,X46,X47) = k2_enumset1(X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X48,X49,X50,X51,X52] : k4_enumset1(X48,X48,X49,X50,X51,X52) = k3_enumset1(X48,X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_26,plain,(
    ! [X53,X54,X55,X56,X57,X58] : k5_enumset1(X53,X53,X54,X55,X56,X57,X58) = k4_enumset1(X53,X54,X55,X56,X57,X58) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_27,plain,(
    ! [X59,X60,X61,X62,X63,X64,X65] : k6_enumset1(X59,X59,X60,X61,X62,X63,X64,X65) = k5_enumset1(X59,X60,X61,X62,X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_28,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0)
    & ( esk6_0 != k1_tarski(esk5_0)
      | esk7_0 != k1_tarski(esk5_0) )
    & ( esk6_0 != k1_xboole_0
      | esk7_0 != k1_tarski(esk5_0) )
    & ( esk6_0 != k1_tarski(esk5_0)
      | esk7_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_29,plain,(
    ! [X38] : k2_tarski(X38,X38) = k1_tarski(X38) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_30,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X16 != k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | r2_hidden(X18,X16)
        | X16 != k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k2_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k2_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X21)
        | r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k2_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_31,plain,(
    ! [X31,X32,X33,X34,X35,X36] :
      ( ( ~ r2_hidden(X33,X32)
        | X33 = X31
        | X32 != k1_tarski(X31) )
      & ( X34 != X31
        | r2_hidden(X34,X32)
        | X32 != k1_tarski(X31) )
      & ( ~ r2_hidden(esk4_2(X35,X36),X36)
        | esk4_2(X35,X36) != X35
        | X36 = k1_tarski(X35) )
      & ( r2_hidden(esk4_2(X35,X36),X36)
        | esk4_2(X35,X36) = X35
        | X36 = k1_tarski(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_32,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_33,plain,(
    ! [X23] :
      ( X23 = k1_xboole_0
      | r2_hidden(esk3_1(X23),X23) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( k1_tarski(esk5_0) = k2_xboole_0(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_22]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_50,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_42]),c_0_22]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_49])).

fof(c_0_55,plain,(
    ! [X68,X69,X70] :
      ( ( r2_hidden(X68,X70)
        | ~ r1_tarski(k2_tarski(X68,X69),X70) )
      & ( r2_hidden(X69,X70)
        | ~ r1_tarski(k2_tarski(X68,X69),X70) )
      & ( ~ r2_hidden(X68,X70)
        | ~ r2_hidden(X69,X70)
        | r1_tarski(k2_tarski(X68,X69),X70) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk3_1(esk6_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_53])).

fof(c_0_59,plain,(
    ! [X25,X26] :
      ( ( r1_tarski(X25,X26)
        | X25 != X26 )
      & ( r1_tarski(X26,X25)
        | X25 != X26 )
      & ( ~ r1_tarski(X25,X26)
        | ~ r1_tarski(X26,X25)
        | X25 = X26 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_46])).

cnf(c_0_61,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( esk3_1(esk6_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,X1),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_52])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk3_1(esk7_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_48])).

cnf(c_0_67,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_22]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_68,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_62])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_70,negated_conjecture,
    ( esk1_2(esk6_0,X1) = esk5_0
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_63])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_22]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_65])).

fof(c_0_73,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k2_xboole_0(X27,X28) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_74,negated_conjecture,
    ( esk3_1(esk7_0) = esk5_0
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,esk5_0),esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( esk6_0 != k1_tarski(esk5_0)
    | esk7_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_81,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_82,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_68])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_84,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_85,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( esk6_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | esk7_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_42]),c_0_42]),c_0_22]),c_0_22]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

cnf(c_0_87,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk6_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])])).

cnf(c_0_88,negated_conjecture,
    ( esk6_0 != k1_tarski(esk5_0)
    | esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_89,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk7_0
    | esk7_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_48])).

cnf(c_0_90,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 != esk6_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk7_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_92,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | esk6_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_42]),c_0_22]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_93,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_87]),c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk7_0 != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_42]),c_0_22]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_95,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_87])).

cnf(c_0_96,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95])])).

cnf(c_0_97,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_89,c_0_96])).

cnf(c_0_98,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_84,c_0_72])).

cnf(c_0_99,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_95]),c_0_95]),c_0_95]),c_0_95]),c_0_95]),c_0_95]),c_0_95]),c_0_97]),c_0_98]),c_0_99]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.19/0.44  # and selection function GSelectMinInfpos.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.028 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.44  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.44  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.19/0.44  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.44  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.44  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.44  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.44  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.44  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.44  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.44  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.19/0.44  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.44  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.44  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.44  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.19/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.44  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.44  fof(c_0_17, plain, ![X66, X67]:k3_tarski(k2_tarski(X66,X67))=k2_xboole_0(X66,X67), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.44  fof(c_0_18, plain, ![X39, X40]:k1_enumset1(X39,X39,X40)=k2_tarski(X39,X40), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.44  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.19/0.44  fof(c_0_20, plain, ![X29, X30]:r1_tarski(X29,k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.44  cnf(c_0_21, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.44  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.44  fof(c_0_23, plain, ![X41, X42, X43]:k2_enumset1(X41,X41,X42,X43)=k1_enumset1(X41,X42,X43), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.44  fof(c_0_24, plain, ![X44, X45, X46, X47]:k3_enumset1(X44,X44,X45,X46,X47)=k2_enumset1(X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.44  fof(c_0_25, plain, ![X48, X49, X50, X51, X52]:k4_enumset1(X48,X48,X49,X50,X51,X52)=k3_enumset1(X48,X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.44  fof(c_0_26, plain, ![X53, X54, X55, X56, X57, X58]:k5_enumset1(X53,X53,X54,X55,X56,X57,X58)=k4_enumset1(X53,X54,X55,X56,X57,X58), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.44  fof(c_0_27, plain, ![X59, X60, X61, X62, X63, X64, X65]:k6_enumset1(X59,X59,X60,X61,X62,X63,X64,X65)=k5_enumset1(X59,X60,X61,X62,X63,X64,X65), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.44  fof(c_0_28, negated_conjecture, (((k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)&(esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_tarski(esk5_0)))&(esk6_0!=k1_xboole_0|esk7_0!=k1_tarski(esk5_0)))&(esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.19/0.44  fof(c_0_29, plain, ![X38]:k2_tarski(X38,X38)=k1_tarski(X38), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.44  fof(c_0_30, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X17,X16)|(r2_hidden(X17,X14)|r2_hidden(X17,X15))|X16!=k2_xboole_0(X14,X15))&((~r2_hidden(X18,X14)|r2_hidden(X18,X16)|X16!=k2_xboole_0(X14,X15))&(~r2_hidden(X18,X15)|r2_hidden(X18,X16)|X16!=k2_xboole_0(X14,X15))))&(((~r2_hidden(esk2_3(X19,X20,X21),X19)|~r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k2_xboole_0(X19,X20))&(~r2_hidden(esk2_3(X19,X20,X21),X20)|~r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k2_xboole_0(X19,X20)))&(r2_hidden(esk2_3(X19,X20,X21),X21)|(r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X20))|X21=k2_xboole_0(X19,X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.19/0.44  fof(c_0_31, plain, ![X31, X32, X33, X34, X35, X36]:(((~r2_hidden(X33,X32)|X33=X31|X32!=k1_tarski(X31))&(X34!=X31|r2_hidden(X34,X32)|X32!=k1_tarski(X31)))&((~r2_hidden(esk4_2(X35,X36),X36)|esk4_2(X35,X36)!=X35|X36=k1_tarski(X35))&(r2_hidden(esk4_2(X35,X36),X36)|esk4_2(X35,X36)=X35|X36=k1_tarski(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.44  fof(c_0_32, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.44  fof(c_0_33, plain, ![X23]:(X23=k1_xboole_0|r2_hidden(esk3_1(X23),X23)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.44  cnf(c_0_34, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.44  cnf(c_0_35, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.44  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.44  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  cnf(c_0_38, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.44  cnf(c_0_39, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.44  cnf(c_0_40, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.44  cnf(c_0_41, negated_conjecture, (k1_tarski(esk5_0)=k2_xboole_0(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_42, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.44  cnf(c_0_43, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.44  cnf(c_0_44, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.44  cnf(c_0_45, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.44  cnf(c_0_46, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.44  cnf(c_0_47, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.19/0.44  cnf(c_0_48, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_22]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 0.19/0.44  cnf(c_0_49, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.19/0.44  cnf(c_0_50, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_42]), c_0_22]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.19/0.44  cnf(c_0_51, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.44  cnf(c_0_52, negated_conjecture, (r1_tarski(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.44  cnf(c_0_53, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.44  cnf(c_0_54, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_49])).
% 0.19/0.44  fof(c_0_55, plain, ![X68, X69, X70]:(((r2_hidden(X68,X70)|~r1_tarski(k2_tarski(X68,X69),X70))&(r2_hidden(X69,X70)|~r1_tarski(k2_tarski(X68,X69),X70)))&(~r2_hidden(X68,X70)|~r2_hidden(X69,X70)|r1_tarski(k2_tarski(X68,X69),X70))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.19/0.44  cnf(c_0_56, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_50])).
% 0.19/0.44  cnf(c_0_57, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk3_1(esk6_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.44  cnf(c_0_58, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_45, c_0_53])).
% 0.19/0.44  fof(c_0_59, plain, ![X25, X26]:(((r1_tarski(X25,X26)|X25!=X26)&(r1_tarski(X26,X25)|X25!=X26))&(~r1_tarski(X25,X26)|~r1_tarski(X26,X25)|X25=X26)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.44  cnf(c_0_60, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_54, c_0_46])).
% 0.19/0.44  cnf(c_0_61, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.44  cnf(c_0_62, negated_conjecture, (esk3_1(esk6_0)=esk5_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.44  cnf(c_0_63, negated_conjecture, (r2_hidden(esk1_2(esk6_0,X1),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_58, c_0_52])).
% 0.19/0.44  cnf(c_0_64, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.44  cnf(c_0_65, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.44  cnf(c_0_66, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk3_1(esk7_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_60, c_0_48])).
% 0.19/0.44  cnf(c_0_67, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_22]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.19/0.44  cnf(c_0_68, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_46, c_0_62])).
% 0.19/0.44  cnf(c_0_69, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.44  cnf(c_0_70, negated_conjecture, (esk1_2(esk6_0,X1)=esk5_0|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_56, c_0_63])).
% 0.19/0.44  cnf(c_0_71, plain, (r2_hidden(X1,X2)|~r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_22]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.19/0.44  cnf(c_0_72, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_65])).
% 0.19/0.44  fof(c_0_73, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k2_xboole_0(X27,X28)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.44  cnf(c_0_74, negated_conjecture, (esk3_1(esk7_0)=esk5_0|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_66])).
% 0.19/0.44  cnf(c_0_75, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,esk5_0),esk6_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.44  cnf(c_0_76, negated_conjecture, (r1_tarski(esk6_0,X1)|~r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.44  cnf(c_0_77, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.44  cnf(c_0_78, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.44  cnf(c_0_79, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_46, c_0_74])).
% 0.19/0.44  cnf(c_0_80, negated_conjecture, (esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_81, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.44  cnf(c_0_82, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_75, c_0_68])).
% 0.19/0.44  cnf(c_0_83, negated_conjecture, (r1_tarski(esk6_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.19/0.44  cnf(c_0_84, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.19/0.44  cnf(c_0_85, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(esk6_0,esk7_0)), inference(spm,[status(thm)],[c_0_76, c_0_79])).
% 0.19/0.44  cnf(c_0_86, negated_conjecture, (esk6_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|esk7_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_42]), c_0_42]), c_0_22]), c_0_22]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 0.19/0.44  cnf(c_0_87, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk6_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])])).
% 0.19/0.44  cnf(c_0_88, negated_conjecture, (esk6_0!=k1_tarski(esk5_0)|esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_89, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk7_0|esk7_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_48])).
% 0.19/0.44  cnf(c_0_90, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0!=esk6_0), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.19/0.44  cnf(c_0_91, negated_conjecture, (esk6_0!=k1_xboole_0|esk7_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_92, negated_conjecture, (esk7_0!=k1_xboole_0|esk6_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_42]), c_0_22]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.19/0.44  cnf(c_0_93, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_87]), c_0_90])).
% 0.19/0.44  cnf(c_0_94, negated_conjecture, (esk6_0!=k1_xboole_0|esk7_0!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_42]), c_0_22]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.19/0.44  cnf(c_0_95, negated_conjecture, (esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_87])).
% 0.19/0.44  cnf(c_0_96, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95])])).
% 0.19/0.44  cnf(c_0_97, negated_conjecture, (esk7_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_89, c_0_96])).
% 0.19/0.44  cnf(c_0_98, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(spm,[status(thm)],[c_0_84, c_0_72])).
% 0.19/0.44  cnf(c_0_99, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_96, c_0_97])).
% 0.19/0.44  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_95]), c_0_95]), c_0_95]), c_0_95]), c_0_95]), c_0_95]), c_0_95]), c_0_97]), c_0_98]), c_0_99]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 101
% 0.19/0.44  # Proof object clause steps            : 66
% 0.19/0.44  # Proof object formula steps           : 35
% 0.19/0.44  # Proof object conjectures             : 34
% 0.19/0.44  # Proof object clause conjectures      : 31
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 24
% 0.19/0.44  # Proof object initial formulas used   : 17
% 0.19/0.44  # Proof object generating inferences   : 24
% 0.19/0.44  # Proof object simplifying inferences  : 101
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 17
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 34
% 0.19/0.44  # Removed in clause preprocessing      : 8
% 0.19/0.44  # Initial clauses in saturation        : 26
% 0.19/0.44  # Processed clauses                    : 344
% 0.19/0.44  # ...of these trivial                  : 5
% 0.19/0.44  # ...subsumed                          : 160
% 0.19/0.44  # ...remaining for further processing  : 178
% 0.19/0.44  # Other redundant clauses eliminated   : 24
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 3
% 0.19/0.44  # Backward-rewritten                   : 98
% 0.19/0.44  # Generated clauses                    : 1381
% 0.19/0.44  # ...of the previous two non-trivial   : 1338
% 0.19/0.44  # Contextual simplify-reflections      : 4
% 0.19/0.44  # Paramodulations                      : 1249
% 0.19/0.44  # Factorizations                       : 108
% 0.19/0.44  # Equation resolutions                 : 24
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 44
% 0.19/0.44  #    Positive orientable unit clauses  : 11
% 0.19/0.44  #    Positive unorientable unit clauses: 0
% 0.19/0.44  #    Negative unit clauses             : 1
% 0.19/0.44  #    Non-unit-clauses                  : 32
% 0.19/0.44  # Current number of unprocessed clauses: 1035
% 0.19/0.44  # ...number of literals in the above   : 5909
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 135
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 5707
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 1246
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 165
% 0.19/0.44  # Unit Clause-clause subsumption calls : 88
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 50
% 0.19/0.44  # BW rewrite match successes           : 5
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 34345
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.093 s
% 0.19/0.44  # System time              : 0.006 s
% 0.19/0.44  # Total time               : 0.098 s
% 0.19/0.44  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
