%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:47 EST 2020

% Result     : Theorem 25.99s
% Output     : CNFRefutation 25.99s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 601 expanded)
%              Number of clauses        :   49 ( 245 expanded)
%              Number of leaves         :   12 ( 170 expanded)
%              Depth                    :   11
%              Number of atoms          :  174 (1312 expanded)
%              Number of equality atoms :   70 ( 704 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t148_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & k3_xboole_0(X2,X3) = k1_tarski(X4)
        & r2_hidden(X4,X1) )
     => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t60_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,X2)
     => ( ( r2_hidden(X3,X2)
          & X1 != X3 )
        | k3_xboole_0(k2_tarski(X1,X3),X2) = k1_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(c_0_12,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X17,X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k3_xboole_0(X14,X15) )
      & ( r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k3_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | ~ r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k3_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k3_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k3_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X20)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k3_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_13,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & k3_xboole_0(esk4_0,esk5_0) = k1_tarski(esk6_0)
    & r2_hidden(esk6_0,esk3_0)
    & k3_xboole_0(esk3_0,esk5_0) != k1_tarski(esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_18,plain,(
    ! [X25] : k2_tarski(X25,X25) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X31,X32,X33,X34] : k3_enumset1(X31,X31,X32,X33,X34) = k2_enumset1(X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_22,plain,(
    ! [X35,X36,X37,X38,X39] : k4_enumset1(X35,X35,X36,X37,X38,X39) = k3_enumset1(X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_23,plain,(
    ! [X40,X41,X42,X43,X44,X45] : k5_enumset1(X40,X40,X41,X42,X43,X44,X45) = k4_enumset1(X40,X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_24,plain,(
    ! [X46,X47,X48,X49,X50,X51,X52] : k6_enumset1(X46,X46,X47,X48,X49,X50,X51,X52) = k5_enumset1(X46,X47,X48,X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_25,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X2,k4_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk5_0) = k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_38,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X4,k4_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) = k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_16]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_38,c_0_16])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_47,plain,(
    ! [X53,X54,X55] :
      ( ( r2_hidden(X55,X54)
        | k3_xboole_0(k2_tarski(X53,X55),X54) = k1_tarski(X53)
        | ~ r2_hidden(X53,X54) )
      & ( X53 != X55
        | k3_xboole_0(k2_tarski(X53,X55),X54) = k1_tarski(X53)
        | ~ r2_hidden(X53,X54) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X4)
    | X4 != k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( X1 = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X2))
    | r2_hidden(esk2_3(esk3_0,X2,X1),esk4_0)
    | r2_hidden(esk2_3(esk3_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_42])).

cnf(c_0_52,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_46,c_0_16])).

cnf(c_0_53,plain,
    ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)) = k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)
    | r2_hidden(esk2_3(esk3_0,X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)
    | r2_hidden(esk2_3(X1,X2,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),esk5_0)
    | r2_hidden(esk2_3(X1,X2,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) != k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_16]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)) = k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)
    | r2_hidden(esk2_3(esk3_0,X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),k4_xboole_0(X2,k4_xboole_0(X2,esk4_0)))
    | ~ r2_hidden(esk2_3(esk3_0,X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)) = k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)
    | r2_hidden(esk2_3(X1,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),esk5_0) ),
    inference(ef,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)) != k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_29]),c_0_30]),c_0_31]),c_0_16]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_64,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)) = k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)
    | r2_hidden(esk2_3(esk3_0,X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X2)))
    | ~ r2_hidden(esk2_3(esk3_0,X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k4_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk3_0)) = k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_64,c_0_16])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_60]),c_0_42]),c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(esk2_3(esk3_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])]),c_0_61])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_69]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:51:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 25.99/26.25  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 25.99/26.25  # and selection function SelectNegativeLiterals.
% 25.99/26.25  #
% 25.99/26.25  # Preprocessing time       : 0.028 s
% 25.99/26.25  # Presaturation interreduction done
% 25.99/26.25  
% 25.99/26.25  # Proof found!
% 25.99/26.25  # SZS status Theorem
% 25.99/26.25  # SZS output start CNFRefutation
% 25.99/26.25  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 25.99/26.25  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 25.99/26.25  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 25.99/26.25  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 25.99/26.25  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 25.99/26.25  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 25.99/26.25  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 25.99/26.25  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 25.99/26.25  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 25.99/26.25  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 25.99/26.25  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 25.99/26.25  fof(t60_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,X2)=>((r2_hidden(X3,X2)&X1!=X3)|k3_xboole_0(k2_tarski(X1,X3),X2)=k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 25.99/26.25  fof(c_0_12, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:((((r2_hidden(X17,X14)|~r2_hidden(X17,X16)|X16!=k3_xboole_0(X14,X15))&(r2_hidden(X17,X15)|~r2_hidden(X17,X16)|X16!=k3_xboole_0(X14,X15)))&(~r2_hidden(X18,X14)|~r2_hidden(X18,X15)|r2_hidden(X18,X16)|X16!=k3_xboole_0(X14,X15)))&((~r2_hidden(esk2_3(X19,X20,X21),X21)|(~r2_hidden(esk2_3(X19,X20,X21),X19)|~r2_hidden(esk2_3(X19,X20,X21),X20))|X21=k3_xboole_0(X19,X20))&((r2_hidden(esk2_3(X19,X20,X21),X19)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k3_xboole_0(X19,X20))&(r2_hidden(esk2_3(X19,X20,X21),X20)|r2_hidden(esk2_3(X19,X20,X21),X21)|X21=k3_xboole_0(X19,X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 25.99/26.25  fof(c_0_13, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 25.99/26.25  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 25.99/26.25  cnf(c_0_15, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 25.99/26.25  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 25.99/26.25  fof(c_0_17, negated_conjecture, (((r1_tarski(esk3_0,esk4_0)&k3_xboole_0(esk4_0,esk5_0)=k1_tarski(esk6_0))&r2_hidden(esk6_0,esk3_0))&k3_xboole_0(esk3_0,esk5_0)!=k1_tarski(esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 25.99/26.25  fof(c_0_18, plain, ![X25]:k2_tarski(X25,X25)=k1_tarski(X25), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 25.99/26.25  fof(c_0_19, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 25.99/26.25  fof(c_0_20, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 25.99/26.25  fof(c_0_21, plain, ![X31, X32, X33, X34]:k3_enumset1(X31,X31,X32,X33,X34)=k2_enumset1(X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 25.99/26.25  fof(c_0_22, plain, ![X35, X36, X37, X38, X39]:k4_enumset1(X35,X35,X36,X37,X38,X39)=k3_enumset1(X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 25.99/26.25  fof(c_0_23, plain, ![X40, X41, X42, X43, X44, X45]:k5_enumset1(X40,X40,X41,X42,X43,X44,X45)=k4_enumset1(X40,X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 25.99/26.25  fof(c_0_24, plain, ![X46, X47, X48, X49, X50, X51, X52]:k6_enumset1(X46,X46,X47,X48,X49,X50,X51,X52)=k5_enumset1(X46,X47,X48,X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 25.99/26.25  fof(c_0_25, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 25.99/26.25  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 25.99/26.25  cnf(c_0_27, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X2,k4_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 25.99/26.25  cnf(c_0_28, negated_conjecture, (k3_xboole_0(esk4_0,esk5_0)=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 25.99/26.25  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 25.99/26.25  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 25.99/26.25  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 25.99/26.25  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 25.99/26.25  cnf(c_0_33, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 25.99/26.25  cnf(c_0_34, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 25.99/26.25  cnf(c_0_35, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 25.99/26.25  cnf(c_0_36, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 25.99/26.25  cnf(c_0_37, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 25.99/26.25  cnf(c_0_38, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 25.99/26.25  cnf(c_0_39, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X4,k4_xboole_0(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_26, c_0_16])).
% 25.99/26.25  cnf(c_0_40, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 25.99/26.25  cnf(c_0_41, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_27])).
% 25.99/26.25  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_16]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 25.99/26.25  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 25.99/26.25  cnf(c_0_44, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_38, c_0_16])).
% 25.99/26.25  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(er,[status(thm)],[c_0_39])).
% 25.99/26.25  cnf(c_0_46, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 25.99/26.25  fof(c_0_47, plain, ![X53, X54, X55]:((r2_hidden(X55,X54)|k3_xboole_0(k2_tarski(X53,X55),X54)=k1_tarski(X53)|~r2_hidden(X53,X54))&(X53!=X55|k3_xboole_0(k2_tarski(X53,X55),X54)=k1_tarski(X53)|~r2_hidden(X53,X54))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).
% 25.99/26.25  cnf(c_0_48, plain, (r2_hidden(X1,X4)|X4!=k4_xboole_0(X2,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_40, c_0_16])).
% 25.99/26.25  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 25.99/26.25  cnf(c_0_50, negated_conjecture, (X1=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X2))|r2_hidden(esk2_3(esk3_0,X2,X1),esk4_0)|r2_hidden(esk2_3(esk3_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 25.99/26.25  cnf(c_0_51, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_45, c_0_42])).
% 25.99/26.25  cnf(c_0_52, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_46, c_0_16])).
% 25.99/26.25  cnf(c_0_53, plain, (k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)|X1!=X2|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 25.99/26.25  cnf(c_0_54, plain, (r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_48])).
% 25.99/26.25  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)|r2_hidden(esk2_3(esk3_0,X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 25.99/26.25  cnf(c_0_56, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)|r2_hidden(esk2_3(X1,X2,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),esk5_0)|r2_hidden(esk2_3(X1,X2,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 25.99/26.25  cnf(c_0_57, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 25.99/26.25  cnf(c_0_58, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|X1!=X2|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_16]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35])).
% 25.99/26.25  cnf(c_0_59, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)|r2_hidden(esk2_3(esk3_0,X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),k4_xboole_0(X2,k4_xboole_0(X2,esk4_0)))|~r2_hidden(esk2_3(esk3_0,X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 25.99/26.25  cnf(c_0_60, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,esk5_0))=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)|r2_hidden(esk2_3(X1,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),esk5_0)), inference(ef,[status(thm)],[c_0_56])).
% 25.99/26.25  cnf(c_0_61, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))!=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_29]), c_0_30]), c_0_31]), c_0_16]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 25.99/26.25  cnf(c_0_62, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_58])).
% 25.99/26.25  cnf(c_0_63, negated_conjecture, (r2_hidden(esk6_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 25.99/26.25  cnf(c_0_64, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 25.99/26.25  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)|r2_hidden(esk2_3(esk3_0,X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X2)))|~r2_hidden(esk2_3(esk3_0,X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 25.99/26.25  cnf(c_0_66, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 25.99/26.25  cnf(c_0_67, negated_conjecture, (k4_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k4_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk3_0))=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 25.99/26.25  cnf(c_0_68, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_64, c_0_16])).
% 25.99/26.25  cnf(c_0_69, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_60]), c_0_42]), c_0_61])).
% 25.99/26.25  cnf(c_0_70, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_66])).
% 25.99/26.25  cnf(c_0_71, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_45, c_0_67])).
% 25.99/26.25  cnf(c_0_72, negated_conjecture, (~r2_hidden(esk2_3(esk3_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])]), c_0_61])).
% 25.99/26.25  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_69]), c_0_72]), ['proof']).
% 25.99/26.25  # SZS output end CNFRefutation
% 25.99/26.25  # Proof object total steps             : 74
% 25.99/26.25  # Proof object clause steps            : 49
% 25.99/26.25  # Proof object formula steps           : 25
% 25.99/26.25  # Proof object conjectures             : 25
% 25.99/26.25  # Proof object clause conjectures      : 22
% 25.99/26.25  # Proof object formula conjectures     : 3
% 25.99/26.25  # Proof object initial clauses used    : 20
% 25.99/26.25  # Proof object initial formulas used   : 12
% 25.99/26.25  # Proof object generating inferences   : 16
% 25.99/26.25  # Proof object simplifying inferences  : 51
% 25.99/26.25  # Training examples: 0 positive, 0 negative
% 25.99/26.25  # Parsed axioms                        : 12
% 25.99/26.25  # Removed by relevancy pruning/SinE    : 0
% 25.99/26.25  # Initial clauses                      : 23
% 25.99/26.25  # Removed in clause preprocessing      : 8
% 25.99/26.25  # Initial clauses in saturation        : 15
% 25.99/26.25  # Processed clauses                    : 40947
% 25.99/26.25  # ...of these trivial                  : 17
% 25.99/26.25  # ...subsumed                          : 34672
% 25.99/26.25  # ...remaining for further processing  : 6257
% 25.99/26.25  # Other redundant clauses eliminated   : 4
% 25.99/26.25  # Clauses deleted for lack of memory   : 0
% 25.99/26.25  # Backward-subsumed                    : 261
% 25.99/26.25  # Backward-rewritten                   : 1558
% 25.99/26.25  # Generated clauses                    : 1948847
% 25.99/26.25  # ...of the previous two non-trivial   : 1910376
% 25.99/26.25  # Contextual simplify-reflections      : 43
% 25.99/26.25  # Paramodulations                      : 1946523
% 25.99/26.25  # Factorizations                       : 2320
% 25.99/26.25  # Equation resolutions                 : 4
% 25.99/26.25  # Propositional unsat checks           : 0
% 25.99/26.25  #    Propositional check models        : 0
% 25.99/26.25  #    Propositional check unsatisfiable : 0
% 25.99/26.25  #    Propositional clauses             : 0
% 25.99/26.26  #    Propositional clauses after purity: 0
% 25.99/26.26  #    Propositional unsat core size     : 0
% 25.99/26.26  #    Propositional preprocessing time  : 0.000
% 25.99/26.26  #    Propositional encoding time       : 0.000
% 25.99/26.26  #    Propositional solver time         : 0.000
% 25.99/26.26  #    Success case prop preproc time    : 0.000
% 25.99/26.26  #    Success case prop encoding time   : 0.000
% 25.99/26.26  #    Success case prop solver time     : 0.000
% 25.99/26.26  # Current number of processed clauses  : 4419
% 25.99/26.26  #    Positive orientable unit clauses  : 41
% 25.99/26.26  #    Positive unorientable unit clauses: 0
% 25.99/26.26  #    Negative unit clauses             : 2
% 25.99/26.26  #    Non-unit-clauses                  : 4376
% 25.99/26.26  # Current number of unprocessed clauses: 1868107
% 25.99/26.26  # ...number of literals in the above   : 10159791
% 25.99/26.26  # Current number of archived formulas  : 0
% 25.99/26.26  # Current number of archived clauses   : 1842
% 25.99/26.26  # Clause-clause subsumption calls (NU) : 5596936
% 25.99/26.26  # Rec. Clause-clause subsumption calls : 552232
% 25.99/26.26  # Non-unit clause-clause subsumptions  : 34966
% 25.99/26.26  # Unit Clause-clause subsumption calls : 5298
% 25.99/26.26  # Rewrite failures with RHS unbound    : 0
% 25.99/26.26  # BW rewrite match attempts            : 239
% 25.99/26.26  # BW rewrite match successes           : 22
% 25.99/26.26  # Condensation attempts                : 0
% 25.99/26.26  # Condensation successes               : 0
% 25.99/26.26  # Termbank termtop insertions          : 144987964
% 26.12/26.32  
% 26.12/26.32  # -------------------------------------------------
% 26.12/26.32  # User time                : 25.231 s
% 26.12/26.32  # System time              : 0.737 s
% 26.12/26.32  # Total time               : 25.967 s
% 26.12/26.32  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
