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
% DateTime   : Thu Dec  3 10:39:51 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  154 (33114 expanded)
%              Number of clauses        :  107 (13409 expanded)
%              Number of leaves         :   23 (9783 expanded)
%              Depth                    :   24
%              Number of atoms          :  314 (42479 expanded)
%              Number of equality atoms :  150 (34628 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   1 average)

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

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(c_0_23,plain,(
    ! [X74,X75] : k3_tarski(k2_tarski(X74,X75)) = k2_xboole_0(X74,X75) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_24,plain,(
    ! [X45,X46] : k1_enumset1(X45,X45,X46) = k2_tarski(X45,X46) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X35,X36] : k3_xboole_0(X35,X36) = k5_xboole_0(k5_xboole_0(X35,X36),k2_xboole_0(X35,X36)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X47,X48,X49] : k2_enumset1(X47,X47,X48,X49) = k1_enumset1(X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X50,X51,X52,X53] : k3_enumset1(X50,X50,X51,X52,X53) = k2_enumset1(X50,X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_31,plain,(
    ! [X29,X30] : r1_tarski(X29,k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_32,plain,(
    ! [X54,X55,X56,X57,X58] : k4_enumset1(X54,X54,X55,X56,X57,X58) = k3_enumset1(X54,X55,X56,X57,X58) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_33,plain,(
    ! [X59,X60,X61,X62,X63,X64] : k5_enumset1(X59,X59,X60,X61,X62,X63,X64) = k4_enumset1(X59,X60,X61,X62,X63,X64) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_34,plain,(
    ! [X65,X66,X67,X68,X69,X70,X71] : k6_enumset1(X65,X65,X66,X67,X68,X69,X70,X71) = k5_enumset1(X65,X66,X67,X68,X69,X70,X71) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_35,negated_conjecture,
    ( k1_tarski(esk3_0) = k2_xboole_0(esk4_0,esk5_0)
    & ( esk4_0 != k1_tarski(esk3_0)
      | esk5_0 != k1_tarski(esk3_0) )
    & ( esk4_0 != k1_xboole_0
      | esk5_0 != k1_tarski(esk3_0) )
    & ( esk4_0 != k1_tarski(esk3_0)
      | esk5_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_36,plain,(
    ! [X44] : k2_tarski(X44,X44) = k1_tarski(X44) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_37,plain,(
    ! [X15] : k3_xboole_0(X15,X15) = X15 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_42,plain,(
    ! [X14] : k2_xboole_0(X14,X14) = X14 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_43,plain,(
    ! [X37,X38,X39,X40,X41,X42] :
      ( ( ~ r2_hidden(X39,X38)
        | X39 = X37
        | X38 != k1_tarski(X37) )
      & ( X40 != X37
        | r2_hidden(X40,X38)
        | X38 != k1_tarski(X37) )
      & ( ~ r2_hidden(esk2_2(X41,X42),X42)
        | esk2_2(X41,X42) != X41
        | X42 = k1_tarski(X41) )
      & ( r2_hidden(esk2_2(X41,X42),X42)
        | esk2_2(X41,X42) = X41
        | X42 = k1_tarski(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_44,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( k1_tarski(esk3_0) = k2_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])).

fof(c_0_53,plain,(
    ! [X34] : k5_xboole_0(X34,X34) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_39]),c_0_40]),c_0_41]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_28]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48])).

fof(c_0_60,plain,(
    ! [X31,X32,X33] : k5_xboole_0(k5_xboole_0(X31,X32),X33) = k5_xboole_0(X31,k5_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_39]),c_0_40]),c_0_41]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_64,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_50]),c_0_28]),c_0_40]),c_0_41]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_65,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

fof(c_0_69,plain,(
    ! [X19,X20] :
      ( ( r1_tarski(X19,X20)
        | X19 != X20 )
      & ( r1_tarski(X20,X19)
        | X19 != X20 )
      & ( ~ r1_tarski(X19,X20)
        | ~ r1_tarski(X20,X19)
        | X19 = X20 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_70,plain,(
    ! [X26] : r1_tarski(k1_xboole_0,X26) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_71,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_62]),c_0_68])).

cnf(c_0_74,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( esk1_2(esk4_0,X1) = esk3_0
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_67])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_73,c_0_62])).

fof(c_0_80,plain,(
    ! [X16,X17,X18] :
      ( ( ~ r2_hidden(X16,X17)
        | ~ r2_hidden(X16,X18)
        | ~ r2_hidden(X16,k5_xboole_0(X17,X18)) )
      & ( r2_hidden(X16,X17)
        | r2_hidden(X16,X18)
        | ~ r2_hidden(X16,k5_xboole_0(X17,X18)) )
      & ( ~ r2_hidden(X16,X17)
        | r2_hidden(X16,X18)
        | r2_hidden(X16,k5_xboole_0(X17,X18)) )
      & ( ~ r2_hidden(X16,X18)
        | r2_hidden(X16,X17)
        | r2_hidden(X16,k5_xboole_0(X17,X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

fof(c_0_81,plain,(
    ! [X27,X28] : r1_tarski(k4_xboole_0(X27,X28),X27) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_82,plain,(
    ! [X21,X22] : k4_xboole_0(X21,X22) = k5_xboole_0(X21,k3_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_83,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_76])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_50]),c_0_28]),c_0_40]),c_0_41]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_78]),c_0_79])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_88,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

fof(c_0_90,plain,(
    ! [X72,X73] :
      ( ( ~ r1_tarski(k1_tarski(X72),X73)
        | r2_hidden(X72,X73) )
      & ( ~ r2_hidden(X72,X73)
        | r1_tarski(k1_tarski(X72),X73) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_91,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_92,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_93,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_85])])).

cnf(c_0_95,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_86])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_97,plain,
    ( r2_hidden(esk1_2(k5_xboole_0(X1,X2),X3),X1)
    | r2_hidden(esk1_2(k5_xboole_0(X1,X2),X3),X2)
    | r1_tarski(k5_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_87,c_0_57])).

cnf(c_0_98,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89]),c_0_52]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_99,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_100,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ r2_hidden(esk3_0,k5_xboole_0(X1,esk4_0))
    | ~ r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_101,plain,
    ( r2_hidden(X1,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_95])).

cnf(c_0_103,plain,
    ( r2_hidden(esk1_2(k5_xboole_0(X1,X2),X2),X1)
    | r1_tarski(k5_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_104,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))),X1) ),
    inference(rw,[status(thm)],[c_0_98,c_0_67])).

cnf(c_0_105,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_50]),c_0_28]),c_0_40]),c_0_41]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_106,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk3_0,X1)
    | ~ r2_hidden(esk3_0,k5_xboole_0(esk4_0,k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_67]),c_0_102])).

cnf(c_0_107,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X2)
    | ~ r2_hidden(esk1_2(k5_xboole_0(X1,X2),X2),k5_xboole_0(X3,X1))
    | ~ r2_hidden(esk1_2(k5_xboole_0(X1,X2),X2),X3) ),
    inference(spm,[status(thm)],[c_0_91,c_0_103])).

cnf(c_0_108,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))),X2) ),
    inference(rw,[status(thm)],[c_0_104,c_0_73])).

cnf(c_0_109,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_92])).

cnf(c_0_110,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk3_0,k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1))
    | ~ r2_hidden(esk3_0,k5_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_73])).

cnf(c_0_111,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,X2))
    | ~ r2_hidden(esk1_2(X1,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X2))
    | ~ r2_hidden(esk1_2(X1,k5_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_107,c_0_86])).

cnf(c_0_112,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_59])).

cnf(c_0_114,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = esk4_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_109]),c_0_66])])).

cnf(c_0_115,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk3_0,k5_xboole_0(esk4_0,k5_xboole_0(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))
    | ~ r2_hidden(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_73]),c_0_102])).

cnf(c_0_116,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),k5_xboole_0(X3,k5_xboole_0(X1,X2)))
    | ~ r2_hidden(esk1_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_111,c_0_73])).

cnf(c_0_117,plain,
    ( r2_hidden(esk1_2(X1,X2),k5_xboole_0(X3,X1))
    | r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_112,c_0_57])).

cnf(c_0_118,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k5_xboole_0(esk4_0,esk5_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_95])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_76])).

cnf(c_0_120,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk3_0,k5_xboole_0(esk4_0,X1))
    | r2_hidden(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_101]),c_0_67]),c_0_86])).

cnf(c_0_121,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),k5_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_67]),c_0_73])).

cnf(c_0_122,negated_conjecture,
    ( k5_xboole_0(esk4_0,esk5_0) = esk4_0
    | esk4_0 = k1_xboole_0
    | ~ r1_tarski(esk4_0,k5_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_118])).

cnf(c_0_123,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk3_0,X1)
    | r1_tarski(esk4_0,k5_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_124,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),k5_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_121,c_0_95])).

cnf(c_0_125,negated_conjecture,
    ( k5_xboole_0(esk4_0,esk5_0) = esk4_0
    | esk4_0 = k1_xboole_0
    | r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_126,negated_conjecture,
    ( esk4_0 != k1_tarski(esk3_0)
    | esk5_0 != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_127,plain,
    ( r2_hidden(esk1_2(X1,X2),k5_xboole_0(X2,X3))
    | r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_124,c_0_73])).

cnf(c_0_128,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_125]),c_0_62])).

cnf(c_0_129,negated_conjecture,
    ( esk4_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk5_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_50]),c_0_50]),c_0_28]),c_0_28]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48])).

cnf(c_0_130,plain,
    ( r2_hidden(esk1_2(X1,X2),k5_xboole_0(X2,X1))
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_127,c_0_57])).

cnf(c_0_131,negated_conjecture,
    ( X1 = esk4_0
    | r2_hidden(esk3_0,esk4_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_84])).

cnf(c_0_132,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_119,c_0_128])).

cnf(c_0_133,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 != esk4_0 ),
    inference(spm,[status(thm)],[c_0_129,c_0_114])).

cnf(c_0_134,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(k5_xboole_0(X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_56,c_0_130])).

cnf(c_0_135,negated_conjecture,
    ( k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = esk4_0
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_131,c_0_113])).

cnf(c_0_136,negated_conjecture,
    ( esk4_0 != k1_tarski(esk3_0)
    | esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_137,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | ~ r1_tarski(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_132]),c_0_133])).

cnf(c_0_138,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_118]),c_0_96])).

cnf(c_0_139,negated_conjecture,
    ( k5_xboole_0(esk5_0,k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1)) = k5_xboole_0(esk4_0,X1)
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_135])).

cnf(c_0_140,negated_conjecture,
    ( k5_xboole_0(X1,k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1))) = esk4_0
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_131,c_0_108])).

cnf(c_0_141,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | esk5_0 != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_142,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk4_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_136,c_0_50]),c_0_28]),c_0_40]),c_0_41]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_143,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_144,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) = k5_xboole_0(esk4_0,esk5_0)
    | r2_hidden(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_95])).

cnf(c_0_145,plain,
    ( k5_xboole_0(X1,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_108])).

cnf(c_0_146,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_91,c_0_94])).

cnf(c_0_147,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | esk5_0 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_141,c_0_50]),c_0_28]),c_0_40]),c_0_41]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_148,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_114])).

cnf(c_0_149,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) = esk5_0
    | r2_hidden(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_144]),c_0_73])).

cnf(c_0_150,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_145]),c_0_79])).

cnf(c_0_151,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_94]),c_0_62])).

cnf(c_0_152,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_147,c_0_148])])).

cnf(c_0_153,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_149,c_0_148]),c_0_148]),c_0_148]),c_0_148]),c_0_148]),c_0_148]),c_0_148]),c_0_150]),c_0_148]),c_0_151]),c_0_152]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:38:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.91/1.07  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.91/1.07  # and selection function GSelectMinInfpos.
% 0.91/1.07  #
% 0.91/1.07  # Preprocessing time       : 0.028 s
% 0.91/1.07  # Presaturation interreduction done
% 0.91/1.07  
% 0.91/1.07  # Proof found!
% 0.91/1.07  # SZS status Theorem
% 0.91/1.07  # SZS output start CNFRefutation
% 0.91/1.07  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.91/1.07  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.91/1.07  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.91/1.07  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.91/1.07  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.91/1.07  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.91/1.07  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.91/1.07  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.91/1.07  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.91/1.07  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.91/1.07  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.91/1.07  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.91/1.07  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.91/1.07  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.91/1.07  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.91/1.07  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.91/1.07  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.91/1.07  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.91/1.07  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.91/1.07  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.91/1.07  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.91/1.07  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.91/1.07  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.91/1.07  fof(c_0_23, plain, ![X74, X75]:k3_tarski(k2_tarski(X74,X75))=k2_xboole_0(X74,X75), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.91/1.07  fof(c_0_24, plain, ![X45, X46]:k1_enumset1(X45,X45,X46)=k2_tarski(X45,X46), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.91/1.07  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.91/1.07  fof(c_0_26, plain, ![X35, X36]:k3_xboole_0(X35,X36)=k5_xboole_0(k5_xboole_0(X35,X36),k2_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.91/1.07  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.91/1.07  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.91/1.07  fof(c_0_29, plain, ![X47, X48, X49]:k2_enumset1(X47,X47,X48,X49)=k1_enumset1(X47,X48,X49), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.91/1.07  fof(c_0_30, plain, ![X50, X51, X52, X53]:k3_enumset1(X50,X50,X51,X52,X53)=k2_enumset1(X50,X51,X52,X53), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.91/1.07  fof(c_0_31, plain, ![X29, X30]:r1_tarski(X29,k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.91/1.07  fof(c_0_32, plain, ![X54, X55, X56, X57, X58]:k4_enumset1(X54,X54,X55,X56,X57,X58)=k3_enumset1(X54,X55,X56,X57,X58), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.91/1.07  fof(c_0_33, plain, ![X59, X60, X61, X62, X63, X64]:k5_enumset1(X59,X59,X60,X61,X62,X63,X64)=k4_enumset1(X59,X60,X61,X62,X63,X64), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.91/1.07  fof(c_0_34, plain, ![X65, X66, X67, X68, X69, X70, X71]:k6_enumset1(X65,X65,X66,X67,X68,X69,X70,X71)=k5_enumset1(X65,X66,X67,X68,X69,X70,X71), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.91/1.07  fof(c_0_35, negated_conjecture, (((k1_tarski(esk3_0)=k2_xboole_0(esk4_0,esk5_0)&(esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_tarski(esk3_0)))&(esk4_0!=k1_xboole_0|esk5_0!=k1_tarski(esk3_0)))&(esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.91/1.07  fof(c_0_36, plain, ![X44]:k2_tarski(X44,X44)=k1_tarski(X44), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.91/1.07  fof(c_0_37, plain, ![X15]:k3_xboole_0(X15,X15)=X15, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.91/1.07  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.91/1.07  cnf(c_0_39, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.91/1.07  cnf(c_0_40, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.91/1.07  cnf(c_0_41, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.91/1.07  fof(c_0_42, plain, ![X14]:k2_xboole_0(X14,X14)=X14, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.91/1.07  fof(c_0_43, plain, ![X37, X38, X39, X40, X41, X42]:(((~r2_hidden(X39,X38)|X39=X37|X38!=k1_tarski(X37))&(X40!=X37|r2_hidden(X40,X38)|X38!=k1_tarski(X37)))&((~r2_hidden(esk2_2(X41,X42),X42)|esk2_2(X41,X42)!=X41|X42=k1_tarski(X41))&(r2_hidden(esk2_2(X41,X42),X42)|esk2_2(X41,X42)=X41|X42=k1_tarski(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.91/1.07  fof(c_0_44, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.91/1.07  cnf(c_0_45, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.91/1.07  cnf(c_0_46, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.91/1.07  cnf(c_0_47, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.91/1.07  cnf(c_0_48, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.91/1.07  cnf(c_0_49, negated_conjecture, (k1_tarski(esk3_0)=k2_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.91/1.07  cnf(c_0_50, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.91/1.07  cnf(c_0_51, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.91/1.07  cnf(c_0_52, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])).
% 0.91/1.07  fof(c_0_53, plain, ![X34]:k5_xboole_0(X34,X34)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.91/1.07  cnf(c_0_54, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.91/1.07  cnf(c_0_55, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.91/1.07  cnf(c_0_56, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.91/1.07  cnf(c_0_57, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.91/1.07  cnf(c_0_58, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_39]), c_0_40]), c_0_41]), c_0_46]), c_0_47]), c_0_48])).
% 0.91/1.07  cnf(c_0_59, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_28]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48])).
% 0.91/1.07  fof(c_0_60, plain, ![X31, X32, X33]:k5_xboole_0(k5_xboole_0(X31,X32),X33)=k5_xboole_0(X31,k5_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.91/1.07  cnf(c_0_61, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_46]), c_0_47]), c_0_48])).
% 0.91/1.07  cnf(c_0_62, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.91/1.07  cnf(c_0_63, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_39]), c_0_40]), c_0_41]), c_0_46]), c_0_47]), c_0_48])).
% 0.91/1.07  cnf(c_0_64, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_50]), c_0_28]), c_0_40]), c_0_41]), c_0_46]), c_0_47]), c_0_48])).
% 0.91/1.07  cnf(c_0_65, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.91/1.07  cnf(c_0_66, negated_conjecture, (r1_tarski(esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.91/1.07  cnf(c_0_67, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.91/1.07  cnf(c_0_68, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.91/1.07  fof(c_0_69, plain, ![X19, X20]:(((r1_tarski(X19,X20)|X19!=X20)&(r1_tarski(X20,X19)|X19!=X20))&(~r1_tarski(X19,X20)|~r1_tarski(X20,X19)|X19=X20)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.91/1.07  fof(c_0_70, plain, ![X26]:r1_tarski(k1_xboole_0,X26), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.91/1.07  cnf(c_0_71, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_64])).
% 0.91/1.07  cnf(c_0_72, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.91/1.07  cnf(c_0_73, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_62]), c_0_68])).
% 0.91/1.07  cnf(c_0_74, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.91/1.07  cnf(c_0_75, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.91/1.07  cnf(c_0_76, negated_conjecture, (esk1_2(esk4_0,X1)=esk3_0|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.91/1.07  cnf(c_0_77, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.91/1.07  cnf(c_0_78, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_67])).
% 0.91/1.07  cnf(c_0_79, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_73, c_0_62])).
% 0.91/1.07  fof(c_0_80, plain, ![X16, X17, X18]:(((~r2_hidden(X16,X17)|~r2_hidden(X16,X18)|~r2_hidden(X16,k5_xboole_0(X17,X18)))&(r2_hidden(X16,X17)|r2_hidden(X16,X18)|~r2_hidden(X16,k5_xboole_0(X17,X18))))&((~r2_hidden(X16,X17)|r2_hidden(X16,X18)|r2_hidden(X16,k5_xboole_0(X17,X18)))&(~r2_hidden(X16,X18)|r2_hidden(X16,X17)|r2_hidden(X16,k5_xboole_0(X17,X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.91/1.07  fof(c_0_81, plain, ![X27, X28]:r1_tarski(k4_xboole_0(X27,X28),X27), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.91/1.07  fof(c_0_82, plain, ![X21, X22]:k4_xboole_0(X21,X22)=k5_xboole_0(X21,k3_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.91/1.07  cnf(c_0_83, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.91/1.07  cnf(c_0_84, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_76])).
% 0.91/1.07  cnf(c_0_85, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_50]), c_0_28]), c_0_40]), c_0_41]), c_0_46]), c_0_47]), c_0_48])).
% 0.91/1.07  cnf(c_0_86, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_78]), c_0_79])).
% 0.91/1.07  cnf(c_0_87, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.91/1.07  cnf(c_0_88, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.91/1.07  cnf(c_0_89, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.91/1.07  fof(c_0_90, plain, ![X72, X73]:((~r1_tarski(k1_tarski(X72),X73)|r2_hidden(X72,X73))&(~r2_hidden(X72,X73)|r1_tarski(k1_tarski(X72),X73))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.91/1.07  cnf(c_0_91, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.91/1.07  cnf(c_0_92, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.91/1.07  cnf(c_0_93, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.91/1.07  cnf(c_0_94, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_85])])).
% 0.91/1.07  cnf(c_0_95, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_73, c_0_86])).
% 0.91/1.07  cnf(c_0_96, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.91/1.07  cnf(c_0_97, plain, (r2_hidden(esk1_2(k5_xboole_0(X1,X2),X3),X1)|r2_hidden(esk1_2(k5_xboole_0(X1,X2),X3),X2)|r1_tarski(k5_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_87, c_0_57])).
% 0.91/1.07  cnf(c_0_98, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89]), c_0_52]), c_0_46]), c_0_47]), c_0_48])).
% 0.91/1.07  cnf(c_0_99, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.91/1.07  cnf(c_0_100, negated_conjecture, (esk4_0=k1_xboole_0|~r2_hidden(esk3_0,k5_xboole_0(X1,esk4_0))|~r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.91/1.07  cnf(c_0_101, plain, (r2_hidden(X1,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.91/1.07  cnf(c_0_102, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_67, c_0_95])).
% 0.91/1.07  cnf(c_0_103, plain, (r2_hidden(esk1_2(k5_xboole_0(X1,X2),X2),X1)|r1_tarski(k5_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.91/1.07  cnf(c_0_104, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))),X1)), inference(rw,[status(thm)],[c_0_98, c_0_67])).
% 0.91/1.07  cnf(c_0_105, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_50]), c_0_28]), c_0_40]), c_0_41]), c_0_46]), c_0_47]), c_0_48])).
% 0.91/1.07  cnf(c_0_106, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk3_0,X1)|~r2_hidden(esk3_0,k5_xboole_0(esk4_0,k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_67]), c_0_102])).
% 0.91/1.07  cnf(c_0_107, plain, (r1_tarski(k5_xboole_0(X1,X2),X2)|~r2_hidden(esk1_2(k5_xboole_0(X1,X2),X2),k5_xboole_0(X3,X1))|~r2_hidden(esk1_2(k5_xboole_0(X1,X2),X2),X3)), inference(spm,[status(thm)],[c_0_91, c_0_103])).
% 0.91/1.07  cnf(c_0_108, plain, (r1_tarski(k5_xboole_0(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))),X2)), inference(rw,[status(thm)],[c_0_104, c_0_73])).
% 0.91/1.07  cnf(c_0_109, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_105, c_0_92])).
% 0.91/1.07  cnf(c_0_110, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk3_0,k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1))|~r2_hidden(esk3_0,k5_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_106, c_0_73])).
% 0.91/1.07  cnf(c_0_111, plain, (r1_tarski(X1,k5_xboole_0(X1,X2))|~r2_hidden(esk1_2(X1,k5_xboole_0(X1,X2)),k5_xboole_0(X3,X2))|~r2_hidden(esk1_2(X1,k5_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_107, c_0_86])).
% 0.91/1.07  cnf(c_0_112, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X3,X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.91/1.07  cnf(c_0_113, negated_conjecture, (r1_tarski(k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),esk4_0)), inference(spm,[status(thm)],[c_0_108, c_0_59])).
% 0.91/1.07  cnf(c_0_114, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=esk4_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_109]), c_0_66])])).
% 0.91/1.07  cnf(c_0_115, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk3_0,k5_xboole_0(esk4_0,k5_xboole_0(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))|~r2_hidden(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_73]), c_0_102])).
% 0.91/1.07  cnf(c_0_116, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),k5_xboole_0(X3,k5_xboole_0(X1,X2)))|~r2_hidden(esk1_2(X1,X2),X3)), inference(spm,[status(thm)],[c_0_111, c_0_73])).
% 0.91/1.07  cnf(c_0_117, plain, (r2_hidden(esk1_2(X1,X2),k5_xboole_0(X3,X1))|r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_112, c_0_57])).
% 0.91/1.07  cnf(c_0_118, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k5_xboole_0(esk4_0,esk5_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_95])).
% 0.91/1.07  cnf(c_0_119, negated_conjecture, (r1_tarski(esk4_0,X1)|~r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_96, c_0_76])).
% 0.91/1.07  cnf(c_0_120, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk3_0,k5_xboole_0(esk4_0,X1))|r2_hidden(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_101]), c_0_67]), c_0_86])).
% 0.91/1.07  cnf(c_0_121, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),k5_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_67]), c_0_73])).
% 0.91/1.07  cnf(c_0_122, negated_conjecture, (k5_xboole_0(esk4_0,esk5_0)=esk4_0|esk4_0=k1_xboole_0|~r1_tarski(esk4_0,k5_xboole_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_74, c_0_118])).
% 0.91/1.07  cnf(c_0_123, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk3_0,X1)|r1_tarski(esk4_0,k5_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 0.91/1.07  cnf(c_0_124, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),k5_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_121, c_0_95])).
% 0.91/1.07  cnf(c_0_125, negated_conjecture, (k5_xboole_0(esk4_0,esk5_0)=esk4_0|esk4_0=k1_xboole_0|r2_hidden(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_122, c_0_123])).
% 0.91/1.07  cnf(c_0_126, negated_conjecture, (esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.91/1.07  cnf(c_0_127, plain, (r2_hidden(esk1_2(X1,X2),k5_xboole_0(X2,X3))|r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)), inference(spm,[status(thm)],[c_0_124, c_0_73])).
% 0.91/1.07  cnf(c_0_128, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_125]), c_0_62])).
% 0.91/1.07  cnf(c_0_129, negated_conjecture, (esk4_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk5_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_50]), c_0_50]), c_0_28]), c_0_28]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48])).
% 0.91/1.07  cnf(c_0_130, plain, (r2_hidden(esk1_2(X1,X2),k5_xboole_0(X2,X1))|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_127, c_0_57])).
% 0.91/1.07  cnf(c_0_131, negated_conjecture, (X1=esk4_0|r2_hidden(esk3_0,esk4_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_74, c_0_84])).
% 0.91/1.07  cnf(c_0_132, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|r1_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_119, c_0_128])).
% 0.91/1.07  cnf(c_0_133, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0!=esk4_0), inference(spm,[status(thm)],[c_0_129, c_0_114])).
% 0.91/1.07  cnf(c_0_134, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(k5_xboole_0(X2,X1),X3)), inference(spm,[status(thm)],[c_0_56, c_0_130])).
% 0.91/1.07  cnf(c_0_135, negated_conjecture, (k5_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=esk4_0|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_131, c_0_113])).
% 0.91/1.07  cnf(c_0_136, negated_conjecture, (esk4_0!=k1_tarski(esk3_0)|esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.91/1.07  cnf(c_0_137, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0|~r1_tarski(esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_132]), c_0_133])).
% 0.91/1.07  cnf(c_0_138, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_118]), c_0_96])).
% 0.91/1.07  cnf(c_0_139, negated_conjecture, (k5_xboole_0(esk5_0,k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1))=k5_xboole_0(esk4_0,X1)|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_67, c_0_135])).
% 0.91/1.07  cnf(c_0_140, negated_conjecture, (k5_xboole_0(X1,k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1)))=esk4_0|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_131, c_0_108])).
% 0.91/1.07  cnf(c_0_141, negated_conjecture, (esk4_0!=k1_xboole_0|esk5_0!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.91/1.07  cnf(c_0_142, negated_conjecture, (esk5_0!=k1_xboole_0|esk4_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_136, c_0_50]), c_0_28]), c_0_40]), c_0_41]), c_0_46]), c_0_47]), c_0_48])).
% 0.91/1.07  cnf(c_0_143, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 0.91/1.07  cnf(c_0_144, negated_conjecture, (k5_xboole_0(esk4_0,k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))=k5_xboole_0(esk4_0,esk5_0)|r2_hidden(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_95])).
% 0.91/1.07  cnf(c_0_145, plain, (k5_xboole_0(X1,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_108])).
% 0.91/1.07  cnf(c_0_146, plain, (~r2_hidden(X1,k5_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_91, c_0_94])).
% 0.91/1.07  cnf(c_0_147, negated_conjecture, (esk4_0!=k1_xboole_0|esk5_0!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_141, c_0_50]), c_0_28]), c_0_40]), c_0_41]), c_0_46]), c_0_47]), c_0_48])).
% 0.91/1.07  cnf(c_0_148, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_114])).
% 0.91/1.07  cnf(c_0_149, negated_conjecture, (k3_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))=esk5_0|r2_hidden(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_144]), c_0_73])).
% 0.91/1.07  cnf(c_0_150, plain, (k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_145]), c_0_79])).
% 0.91/1.07  cnf(c_0_151, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_94]), c_0_62])).
% 0.91/1.07  cnf(c_0_152, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_147, c_0_148])])).
% 0.91/1.07  cnf(c_0_153, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_149, c_0_148]), c_0_148]), c_0_148]), c_0_148]), c_0_148]), c_0_148]), c_0_148]), c_0_150]), c_0_148]), c_0_151]), c_0_152]), ['proof']).
% 0.91/1.07  # SZS output end CNFRefutation
% 0.91/1.07  # Proof object total steps             : 154
% 0.91/1.07  # Proof object clause steps            : 107
% 0.91/1.07  # Proof object formula steps           : 47
% 0.91/1.07  # Proof object conjectures             : 44
% 0.91/1.07  # Proof object clause conjectures      : 41
% 0.91/1.07  # Proof object formula conjectures     : 3
% 0.91/1.07  # Proof object initial clauses used    : 32
% 0.91/1.07  # Proof object initial formulas used   : 23
% 0.91/1.07  # Proof object generating inferences   : 55
% 0.91/1.07  # Proof object simplifying inferences  : 127
% 0.91/1.07  # Training examples: 0 positive, 0 negative
% 0.91/1.07  # Parsed axioms                        : 24
% 0.91/1.07  # Removed by relevancy pruning/SinE    : 0
% 0.91/1.07  # Initial clauses                      : 38
% 0.91/1.07  # Removed in clause preprocessing      : 10
% 0.91/1.07  # Initial clauses in saturation        : 28
% 0.91/1.07  # Processed clauses                    : 2974
% 0.91/1.07  # ...of these trivial                  : 19
% 0.91/1.07  # ...subsumed                          : 2307
% 0.91/1.07  # ...remaining for further processing  : 647
% 0.91/1.07  # Other redundant clauses eliminated   : 40
% 0.91/1.07  # Clauses deleted for lack of memory   : 0
% 0.91/1.07  # Backward-subsumed                    : 105
% 0.91/1.07  # Backward-rewritten                   : 332
% 0.91/1.07  # Generated clauses                    : 37648
% 0.91/1.07  # ...of the previous two non-trivial   : 35952
% 0.91/1.07  # Contextual simplify-reflections      : 6
% 0.91/1.07  # Paramodulations                      : 37557
% 0.91/1.07  # Factorizations                       : 52
% 0.91/1.07  # Equation resolutions                 : 40
% 0.91/1.07  # Propositional unsat checks           : 0
% 0.91/1.07  #    Propositional check models        : 0
% 0.91/1.07  #    Propositional check unsatisfiable : 0
% 0.91/1.07  #    Propositional clauses             : 0
% 0.91/1.07  #    Propositional clauses after purity: 0
% 0.91/1.07  #    Propositional unsat core size     : 0
% 0.91/1.07  #    Propositional preprocessing time  : 0.000
% 0.91/1.07  #    Propositional encoding time       : 0.000
% 0.91/1.07  #    Propositional solver time         : 0.000
% 0.91/1.07  #    Success case prop preproc time    : 0.000
% 0.91/1.07  #    Success case prop encoding time   : 0.000
% 0.91/1.07  #    Success case prop solver time     : 0.000
% 0.91/1.07  # Current number of processed clauses  : 179
% 0.91/1.07  #    Positive orientable unit clauses  : 25
% 0.91/1.07  #    Positive unorientable unit clauses: 3
% 0.91/1.07  #    Negative unit clauses             : 3
% 0.91/1.07  #    Non-unit-clauses                  : 148
% 0.91/1.07  # Current number of unprocessed clauses: 32830
% 0.91/1.07  # ...number of literals in the above   : 164218
% 0.91/1.07  # Current number of archived formulas  : 0
% 0.91/1.07  # Current number of archived clauses   : 474
% 0.91/1.07  # Clause-clause subsumption calls (NU) : 23360
% 0.91/1.07  # Rec. Clause-clause subsumption calls : 11096
% 0.91/1.07  # Non-unit clause-clause subsumptions  : 2231
% 0.91/1.07  # Unit Clause-clause subsumption calls : 82
% 0.91/1.07  # Rewrite failures with RHS unbound    : 0
% 0.91/1.07  # BW rewrite match attempts            : 117
% 0.91/1.07  # BW rewrite match successes           : 68
% 0.91/1.07  # Condensation attempts                : 0
% 0.91/1.07  # Condensation successes               : 0
% 0.91/1.07  # Termbank termtop insertions          : 867084
% 0.91/1.08  
% 0.91/1.08  # -------------------------------------------------
% 0.91/1.08  # User time                : 0.725 s
% 0.91/1.08  # System time              : 0.020 s
% 0.91/1.08  # Total time               : 0.744 s
% 0.91/1.08  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
