%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 (2441 expanded)
%              Number of clauses        :   67 ( 928 expanded)
%              Number of leaves         :   19 ( 744 expanded)
%              Depth                    :   19
%              Number of atoms          :  246 (3458 expanded)
%              Number of equality atoms :   99 (2771 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(c_0_19,plain,(
    ! [X62,X63] : k3_tarski(k2_tarski(X62,X63)) = k2_xboole_0(X62,X63) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X31,X32] : k1_enumset1(X31,X31,X32) = k2_tarski(X31,X32) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X58,X59] :
      ( r2_hidden(X58,X59)
      | r1_xboole_0(k1_tarski(X58),X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_23,plain,(
    ! [X30] : k2_tarski(X30,X30) = k1_tarski(X30) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_24,plain,(
    ! [X33,X34,X35] : k2_enumset1(X33,X33,X34,X35) = k1_enumset1(X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X36,X37,X38,X39] : k3_enumset1(X36,X36,X37,X38,X39) = k2_enumset1(X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,plain,(
    ! [X40,X41,X42,X43,X44] : k4_enumset1(X40,X40,X41,X42,X43,X44) = k3_enumset1(X40,X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_27,plain,(
    ! [X45,X46,X47,X48,X49,X50] : k5_enumset1(X45,X45,X46,X47,X48,X49,X50) = k4_enumset1(X45,X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_28,plain,(
    ! [X51,X52,X53,X54,X55,X56,X57] : k6_enumset1(X51,X51,X52,X53,X54,X55,X56,X57) = k5_enumset1(X51,X52,X53,X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_29,plain,(
    ! [X28,X29] : r1_tarski(X28,k2_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_30,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_32,negated_conjecture,
    ( k1_tarski(esk3_0) = k2_xboole_0(esk4_0,esk5_0)
    & ( esk4_0 != k1_tarski(esk3_0)
      | esk5_0 != k1_tarski(esk3_0) )
    & ( esk4_0 != k1_xboole_0
      | esk5_0 != k1_tarski(esk3_0) )
    & ( esk4_0 != k1_tarski(esk3_0)
      | esk5_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_33,plain,(
    ! [X16,X17,X19,X20,X21] :
      ( ( r2_hidden(esk2_2(X16,X17),X16)
        | r1_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_2(X16,X17),X17)
        | r1_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | ~ r1_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_41,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( k1_tarski(esk3_0) = k2_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_31]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_35]),c_0_31]),c_0_43]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

fof(c_0_51,plain,(
    ! [X64,X65,X66] :
      ( ( r2_hidden(X64,X66)
        | ~ r1_tarski(k2_tarski(X64,X65),X66) )
      & ( r2_hidden(X65,X66)
        | ~ r1_tarski(k2_tarski(X64,X65),X66) )
      & ( ~ r2_hidden(X64,X66)
        | ~ r2_hidden(X65,X66)
        | r1_tarski(k2_tarski(X64,X65),X66) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(esk2_2(X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(esk4_0,X1)
    | r2_hidden(esk2_2(esk4_0,X1),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_59,plain,(
    ! [X60,X61] :
      ( ( ~ r1_tarski(X60,k1_tarski(X61))
        | X60 = k1_xboole_0
        | X60 = k1_tarski(X61) )
      & ( X60 != k1_xboole_0
        | r1_tarski(X60,k1_tarski(X61)) )
      & ( X60 != k1_tarski(X61)
        | r1_tarski(X60,k1_tarski(X61)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_60,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_31]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(esk4_0,X1)
    | r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_63,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k2_xboole_0(X22,X23) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(esk4_0,X1)
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,esk3_0),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_35]),c_0_35]),c_0_31]),c_0_31]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

cnf(c_0_66,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(esk4_0,X1)
    | r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = esk4_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_55])).

fof(c_0_69,plain,(
    ! [X25,X26,X27] :
      ( ( r1_xboole_0(X25,k2_xboole_0(X26,X27))
        | ~ r1_xboole_0(X25,X26)
        | ~ r1_xboole_0(X25,X27) )
      & ( r1_xboole_0(X25,X26)
        | ~ r1_xboole_0(X25,k2_xboole_0(X26,X27)) )
      & ( r1_xboole_0(X25,X27)
        | ~ r1_xboole_0(X25,k2_xboole_0(X26,X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_70,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_43]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_71,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_xboole_0(esk4_0,X1)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( esk4_0 != k1_tarski(esk3_0)
    | esk5_0 != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1)) = X1
    | esk4_0 = k1_xboole_0
    | r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( esk4_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk5_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_35]),c_0_35]),c_0_31]),c_0_31]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

cnf(c_0_76,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_43]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

fof(c_0_77,plain,(
    ! [X14,X15] :
      ( ~ r1_xboole_0(X14,X15)
      | r1_xboole_0(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_78,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = esk5_0
    | esk4_0 = k1_xboole_0
    | r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 != esk4_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_68])).

cnf(c_0_80,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(X1,esk5_0)
    | ~ r1_xboole_0(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_50])).

cnf(c_0_82,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_xboole_0(esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_78]),c_0_79])).

cnf(c_0_84,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_80])).

fof(c_0_85,plain,(
    ! [X24] :
      ( ( r1_xboole_0(X24,X24)
        | X24 != k1_xboole_0 )
      & ( X24 = k1_xboole_0
        | ~ r1_xboole_0(X24,X24) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_86,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_xboole_0(X1,esk5_0)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_68])).

cnf(c_0_87,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_xboole_0(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,X2)
    | r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_2(X2,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_80])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_55])).

cnf(c_0_90,negated_conjecture,
    ( esk4_0 != k1_tarski(esk3_0)
    | esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_91,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_xboole_0(esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | esk5_0 != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_96,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk4_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_35]),c_0_31]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_97,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1)) = X1
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_93])).

cnf(c_0_99,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | esk5_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_35]),c_0_31]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_101,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_68])).

cnf(c_0_102,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = esk5_0
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_98])).

cnf(c_0_103,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101])])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_101]),c_0_103]),c_0_104]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.20/0.43  # and selection function GSelectMinInfpos.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.028 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.43  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.20/0.43  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.20/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.43  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.43  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.43  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.43  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.43  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.43  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.43  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.20/0.43  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.20/0.43  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.43  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.20/0.43  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.43  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.20/0.43  fof(c_0_19, plain, ![X62, X63]:k3_tarski(k2_tarski(X62,X63))=k2_xboole_0(X62,X63), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.43  fof(c_0_20, plain, ![X31, X32]:k1_enumset1(X31,X31,X32)=k2_tarski(X31,X32), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.43  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.20/0.43  fof(c_0_22, plain, ![X58, X59]:(r2_hidden(X58,X59)|r1_xboole_0(k1_tarski(X58),X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.20/0.43  fof(c_0_23, plain, ![X30]:k2_tarski(X30,X30)=k1_tarski(X30), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.43  fof(c_0_24, plain, ![X33, X34, X35]:k2_enumset1(X33,X33,X34,X35)=k1_enumset1(X33,X34,X35), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.43  fof(c_0_25, plain, ![X36, X37, X38, X39]:k3_enumset1(X36,X36,X37,X38,X39)=k2_enumset1(X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.43  fof(c_0_26, plain, ![X40, X41, X42, X43, X44]:k4_enumset1(X40,X40,X41,X42,X43,X44)=k3_enumset1(X40,X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.43  fof(c_0_27, plain, ![X45, X46, X47, X48, X49, X50]:k5_enumset1(X45,X45,X46,X47,X48,X49,X50)=k4_enumset1(X45,X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.43  fof(c_0_28, plain, ![X51, X52, X53, X54, X55, X56, X57]:k6_enumset1(X51,X51,X52,X53,X54,X55,X56,X57)=k5_enumset1(X51,X52,X53,X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.43  fof(c_0_29, plain, ![X28, X29]:r1_tarski(X28,k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.43  cnf(c_0_30, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  fof(c_0_32, negated_conjecture, (((k1_tarski(esk3_0)=k2_xboole_0(esk4_0,esk5_0)&(esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_tarski(esk3_0)))&(esk4_0!=k1_xboole_0|esk5_0!=k1_tarski(esk3_0)))&(esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.20/0.43  fof(c_0_33, plain, ![X16, X17, X19, X20, X21]:(((r2_hidden(esk2_2(X16,X17),X16)|r1_xboole_0(X16,X17))&(r2_hidden(esk2_2(X16,X17),X17)|r1_xboole_0(X16,X17)))&(~r2_hidden(X21,X19)|~r2_hidden(X21,X20)|~r1_xboole_0(X19,X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.43  cnf(c_0_34, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.43  cnf(c_0_38, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.43  cnf(c_0_39, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.43  cnf(c_0_40, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.43  fof(c_0_41, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.43  cnf(c_0_42, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_43, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.43  cnf(c_0_44, negated_conjecture, (k1_tarski(esk3_0)=k2_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.43  cnf(c_0_46, plain, (r2_hidden(X1,X2)|r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_31]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.20/0.43  cnf(c_0_47, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.43  cnf(c_0_48, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.43  cnf(c_0_49, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.20/0.43  cnf(c_0_50, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_35]), c_0_31]), c_0_43]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 0.20/0.43  fof(c_0_51, plain, ![X64, X65, X66]:(((r2_hidden(X64,X66)|~r1_tarski(k2_tarski(X64,X65),X66))&(r2_hidden(X65,X66)|~r1_tarski(k2_tarski(X64,X65),X66)))&(~r2_hidden(X64,X66)|~r2_hidden(X65,X66)|r1_tarski(k2_tarski(X64,X65),X66))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.20/0.43  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.43  cnf(c_0_53, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.43  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.43  cnf(c_0_55, negated_conjecture, (r1_tarski(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.43  cnf(c_0_56, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.43  cnf(c_0_57, plain, (r1_xboole_0(X1,X2)|r2_hidden(X3,X2)|~r2_hidden(esk2_2(X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.43  cnf(c_0_58, negated_conjecture, (r1_xboole_0(esk4_0,X1)|r2_hidden(esk2_2(esk4_0,X1),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.43  fof(c_0_59, plain, ![X60, X61]:((~r1_tarski(X60,k1_tarski(X61))|(X60=k1_xboole_0|X60=k1_tarski(X61)))&((X60!=k1_xboole_0|r1_tarski(X60,k1_tarski(X61)))&(X60!=k1_tarski(X61)|r1_tarski(X60,k1_tarski(X61))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.20/0.43  cnf(c_0_60, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_31]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.20/0.43  cnf(c_0_61, negated_conjecture, (r1_xboole_0(esk4_0,X1)|r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.43  cnf(c_0_62, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.43  fof(c_0_63, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k2_xboole_0(X22,X23)=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.43  cnf(c_0_64, negated_conjecture, (r1_xboole_0(esk4_0,X1)|r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,esk3_0),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.43  cnf(c_0_65, plain, (X1=k1_xboole_0|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_35]), c_0_35]), c_0_31]), c_0_31]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 0.20/0.43  cnf(c_0_66, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.43  cnf(c_0_67, negated_conjecture, (r1_xboole_0(esk4_0,X1)|r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_64, c_0_61])).
% 0.20/0.43  cnf(c_0_68, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=esk4_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_55])).
% 0.20/0.43  fof(c_0_69, plain, ![X25, X26, X27]:((r1_xboole_0(X25,k2_xboole_0(X26,X27))|~r1_xboole_0(X25,X26)|~r1_xboole_0(X25,X27))&((r1_xboole_0(X25,X26)|~r1_xboole_0(X25,k2_xboole_0(X26,X27)))&(r1_xboole_0(X25,X27)|~r1_xboole_0(X25,k2_xboole_0(X26,X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.20/0.43  cnf(c_0_70, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_43]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.20/0.43  cnf(c_0_71, negated_conjecture, (esk4_0=k1_xboole_0|r1_xboole_0(esk4_0,X1)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.43  cnf(c_0_72, negated_conjecture, (esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_73, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.43  cnf(c_0_74, negated_conjecture, (k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1))=X1|esk4_0=k1_xboole_0|r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.43  cnf(c_0_75, negated_conjecture, (esk4_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk5_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_35]), c_0_35]), c_0_31]), c_0_31]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 0.20/0.43  cnf(c_0_76, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_43]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.20/0.43  fof(c_0_77, plain, ![X14, X15]:(~r1_xboole_0(X14,X15)|r1_xboole_0(X15,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.43  cnf(c_0_78, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=esk5_0|esk4_0=k1_xboole_0|r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_74])).
% 0.20/0.43  cnf(c_0_79, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0!=esk4_0), inference(spm,[status(thm)],[c_0_75, c_0_68])).
% 0.20/0.43  cnf(c_0_80, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.43  cnf(c_0_81, negated_conjecture, (r1_xboole_0(X1,esk5_0)|~r1_xboole_0(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_76, c_0_50])).
% 0.20/0.43  cnf(c_0_82, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.43  cnf(c_0_83, negated_conjecture, (esk4_0=k1_xboole_0|r1_xboole_0(esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_78]), c_0_79])).
% 0.20/0.43  cnf(c_0_84, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_47, c_0_80])).
% 0.20/0.43  fof(c_0_85, plain, ![X24]:((r1_xboole_0(X24,X24)|X24!=k1_xboole_0)&(X24=k1_xboole_0|~r1_xboole_0(X24,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.20/0.43  cnf(c_0_86, negated_conjecture, (esk4_0=k1_xboole_0|r1_xboole_0(X1,esk5_0)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_81, c_0_68])).
% 0.20/0.43  cnf(c_0_87, negated_conjecture, (esk4_0=k1_xboole_0|r1_xboole_0(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.43  cnf(c_0_88, plain, (r2_hidden(X1,X2)|r1_tarski(X2,X3)|~r2_hidden(esk1_2(X2,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_52, c_0_80])).
% 0.20/0.43  cnf(c_0_89, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_84, c_0_55])).
% 0.20/0.43  cnf(c_0_90, negated_conjecture, (esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_91, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.20/0.43  cnf(c_0_92, negated_conjecture, (esk4_0=k1_xboole_0|r1_xboole_0(esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.43  cnf(c_0_93, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.20/0.43  cnf(c_0_94, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.20/0.43  cnf(c_0_95, negated_conjecture, (esk4_0!=k1_xboole_0|esk5_0!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_96, negated_conjecture, (esk5_0!=k1_xboole_0|esk4_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_35]), c_0_31]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.20/0.43  cnf(c_0_97, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.20/0.43  cnf(c_0_98, negated_conjecture, (k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1))=X1|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_70, c_0_93])).
% 0.20/0.43  cnf(c_0_99, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[c_0_94])).
% 0.20/0.43  cnf(c_0_100, negated_conjecture, (esk4_0!=k1_xboole_0|esk5_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_35]), c_0_31]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.20/0.43  cnf(c_0_101, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_68])).
% 0.20/0.43  cnf(c_0_102, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=esk5_0|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_98])).
% 0.20/0.43  cnf(c_0_103, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_99])).
% 0.20/0.43  cnf(c_0_104, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_101])])).
% 0.20/0.43  cnf(c_0_105, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_101]), c_0_103]), c_0_104]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 106
% 0.20/0.43  # Proof object clause steps            : 67
% 0.20/0.43  # Proof object formula steps           : 39
% 0.20/0.43  # Proof object conjectures             : 34
% 0.20/0.43  # Proof object clause conjectures      : 31
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 26
% 0.20/0.43  # Proof object initial formulas used   : 19
% 0.20/0.43  # Proof object generating inferences   : 27
% 0.20/0.43  # Proof object simplifying inferences  : 95
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 19
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 33
% 0.20/0.43  # Removed in clause preprocessing      : 8
% 0.20/0.43  # Initial clauses in saturation        : 25
% 0.20/0.43  # Processed clauses                    : 862
% 0.20/0.43  # ...of these trivial                  : 8
% 0.20/0.43  # ...subsumed                          : 579
% 0.20/0.43  # ...remaining for further processing  : 274
% 0.20/0.43  # Other redundant clauses eliminated   : 3
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 16
% 0.20/0.43  # Backward-rewritten                   : 159
% 0.20/0.43  # Generated clauses                    : 2265
% 0.20/0.43  # ...of the previous two non-trivial   : 2100
% 0.20/0.43  # Contextual simplify-reflections      : 3
% 0.20/0.43  # Paramodulations                      : 2258
% 0.20/0.43  # Factorizations                       : 4
% 0.20/0.43  # Equation resolutions                 : 3
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 71
% 0.20/0.43  #    Positive orientable unit clauses  : 15
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 3
% 0.20/0.43  #    Non-unit-clauses                  : 53
% 0.20/0.43  # Current number of unprocessed clauses: 1247
% 0.20/0.43  # ...number of literals in the above   : 4087
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 208
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 7287
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 3112
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 581
% 0.20/0.43  # Unit Clause-clause subsumption calls : 28
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 50
% 0.20/0.43  # BW rewrite match successes           : 6
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 42120
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.084 s
% 0.20/0.43  # System time              : 0.004 s
% 0.20/0.43  # Total time               : 0.088 s
% 0.20/0.43  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
