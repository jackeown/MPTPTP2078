%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:03 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  166 (14660 expanded)
%              Number of clauses        :  123 (6375 expanded)
%              Number of leaves         :   21 (4029 expanded)
%              Depth                    :   27
%              Number of atoms          :  258 (21658 expanded)
%              Number of equality atoms :  147 (15374 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t82_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t44_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & X2 != X3
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(t37_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(t87_enumset1,axiom,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(t83_enumset1,axiom,(
    ! [X1,X2] : k3_enumset1(X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

fof(t84_enumset1,axiom,(
    ! [X1,X2,X3] : k4_enumset1(X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t87_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t14_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(c_0_21,plain,(
    ! [X26] :
      ( ( r1_xboole_0(X26,X26)
        | X26 != k1_xboole_0 )
      & ( X26 = k1_xboole_0
        | ~ r1_xboole_0(X26,X26) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_22,plain,(
    ! [X31,X32] : r1_xboole_0(k4_xboole_0(X31,X32),k4_xboole_0(X32,X31)) ),
    inference(variable_rename,[status(thm)],[t82_xboole_1])).

fof(c_0_23,plain,(
    ! [X13,X14] : k2_xboole_0(X13,k4_xboole_0(X14,X13)) = k2_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & X2 != X3
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k2_xboole_0(X21,X22)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_28,plain,(
    ! [X23,X24,X25] : k2_xboole_0(k2_xboole_0(X23,X24),X25) = k2_xboole_0(X23,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_31,plain,(
    ! [X27,X28] : k2_xboole_0(X27,k2_xboole_0(X27,X28)) = k2_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

fof(c_0_32,plain,(
    ! [X61,X62] :
      ( ( ~ r1_tarski(k1_tarski(X61),X62)
        | r2_hidden(X61,X62) )
      & ( ~ r2_hidden(X61,X62)
        | r1_tarski(k1_tarski(X61),X62) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).

fof(c_0_33,plain,(
    ! [X58] : k3_enumset1(X58,X58,X58,X58,X58) = k1_tarski(X58) ),
    inference(variable_rename,[status(thm)],[t87_enumset1])).

fof(c_0_34,negated_conjecture,
    ( k1_tarski(esk2_0) = k2_xboole_0(esk3_0,esk4_0)
    & esk3_0 != esk4_0
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_35,plain,(
    ! [X36,X37,X38,X39,X40] : k3_enumset1(X36,X37,X38,X39,X40) = k2_xboole_0(k1_enumset1(X36,X37,X38),k2_tarski(X39,X40)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

fof(c_0_36,plain,(
    ! [X53,X54] : k3_enumset1(X53,X53,X53,X53,X54) = k2_tarski(X53,X54) ),
    inference(variable_rename,[status(thm)],[t83_enumset1])).

fof(c_0_37,plain,(
    ! [X55,X56,X57] : k4_enumset1(X55,X55,X55,X55,X56,X57) = k1_enumset1(X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t84_enumset1])).

fof(c_0_38,plain,(
    ! [X47,X48,X49,X50,X51,X52] : k5_enumset1(X47,X47,X48,X49,X50,X51,X52) = k4_enumset1(X47,X48,X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_39,plain,(
    ! [X41,X42,X43,X44,X45,X46] : k4_enumset1(X41,X42,X43,X44,X45,X46) = k2_xboole_0(k1_tarski(X41),k3_enumset1(X42,X43,X44,X45,X46)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( k1_tarski(esk2_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_47,plain,(
    ! [X15,X16,X17] : k4_xboole_0(k4_xboole_0(X15,X16),X17) = k4_xboole_0(X15,k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_48,plain,(
    ! [X29,X30] : r1_tarski(X29,k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( k4_enumset1(X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_41]),c_0_43])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_61,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_45]),c_0_52])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk2_0,X1)
    | ~ r1_tarski(k2_xboole_0(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_30]),c_0_29])).

fof(c_0_66,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_67,plain,
    ( r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k5_enumset1(esk2_0,esk2_0,X1,X2,X3,X4,X5) = k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(X1,X2,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_57]),c_0_41])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_40]),c_0_41]),c_0_41])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,k1_xboole_0))) = k2_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_62]),c_0_41]),c_0_41])).

cnf(c_0_71,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_63,c_0_45])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk2_0,k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_59]),c_0_41])).

fof(c_0_73,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(k4_xboole_0(X18,X19),X20)
      | r1_tarski(X18,k2_xboole_0(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_55])).

cnf(c_0_75,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k1_xboole_0)),k2_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_57]),c_0_68]),c_0_57]),c_0_69]),c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_57])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_29]),c_0_41])).

cnf(c_0_81,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_42])).

cnf(c_0_82,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,k2_xboole_0(X1,k1_xboole_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_69])).

cnf(c_0_83,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k1_xboole_0)) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_59]),c_0_80])).

cnf(c_0_86,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,X1),k2_xboole_0(X1,X2))
    | ~ r1_tarski(k1_xboole_0,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_81]),c_0_41]),c_0_55])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk4_0,esk3_0),k2_xboole_0(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_84]),c_0_29])).

cnf(c_0_89,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,k2_xboole_0(X2,X3)))) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk2_0,k2_xboole_0(X1,k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_85]),c_0_41])).

cnf(c_0_91,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,X1),k2_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))) = k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_87]),c_0_41]),c_0_55]),c_0_41]),c_0_41]),c_0_43])).

cnf(c_0_93,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_58])).

cnf(c_0_94,plain,
    ( r1_tarski(k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))),k2_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk2_0,k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_89])).

cnf(c_0_96,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X1,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_69]),c_0_41]),c_0_55])).

cnf(c_0_97,plain,
    ( k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k3_enumset1(X1,X2,X3,X4,X5)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_60])).

cnf(c_0_98,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1))) = k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_92])).

cnf(c_0_99,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_65])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,k1_xboole_0)),k2_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_83]),c_0_69])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_95]),c_0_57])).

fof(c_0_102,plain,(
    ! [X33,X34,X35] :
      ( ~ r1_xboole_0(X33,X34)
      | k2_xboole_0(k4_xboole_0(X35,X33),X34) = k4_xboole_0(k2_xboole_0(X35,X34),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_xboole_1])])).

cnf(c_0_103,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_96]),c_0_88])])).

cnf(c_0_104,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k1_xboole_0)),k2_xboole_0(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_57]),c_0_68]),c_0_57]),c_0_69]),c_0_70])).

cnf(c_0_105,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_29]),c_0_55])).

cnf(c_0_106,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,k4_xboole_0(esk4_0,X1))) = k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_70])).

cnf(c_0_107,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,k1_xboole_0)) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_100]),c_0_101])])).

cnf(c_0_108,plain,
    ( k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_109,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_103]),c_0_103])).

cnf(c_0_110,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k1_xboole_0)),esk3_0)) = k2_xboole_0(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_104])).

cnf(c_0_111,plain,
    ( r1_tarski(k4_xboole_0(X1,k1_xboole_0),k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_105])).

cnf(c_0_112,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,k4_xboole_0(esk4_0,X1))) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_113,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_25])).

cnf(c_0_114,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_40]),c_0_41]),c_0_40])).

cnf(c_0_115,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),X2) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_109]),c_0_41]),c_0_55]),c_0_55])).

fof(c_0_116,plain,(
    ! [X59,X60] :
      ( r2_hidden(X59,X60)
      | r1_xboole_0(k1_tarski(X59),X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_117,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk3_0)) = k2_xboole_0(esk4_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_110,c_0_83])).

cnf(c_0_118,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X2,X1)
    | ~ r1_tarski(k2_xboole_0(X2,X1),k4_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_111])).

cnf(c_0_119,negated_conjecture,
    ( k2_xboole_0(X1,k2_xboole_0(esk4_0,k2_xboole_0(X1,k2_xboole_0(esk3_0,esk4_0)))) = k2_xboole_0(X1,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_112])).

cnf(c_0_120,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_105]),c_0_115]),c_0_105])).

cnf(c_0_121,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_122,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk3_0),X1)) = k2_xboole_0(esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_117]),c_0_41]),c_0_55])).

cnf(c_0_123,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(X1,k2_xboole_0(esk3_0,esk4_0))) = k2_xboole_0(X1,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_120]),c_0_120]),c_0_88])])).

cnf(c_0_124,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) = k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_107]),c_0_41]),c_0_41]),c_0_55])).

cnf(c_0_125,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_121,c_0_45])).

cnf(c_0_126,plain,
    ( k4_xboole_0(k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k1_xboole_0),k3_enumset1(X1,X2,X3,X4,X5)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_60])).

cnf(c_0_127,negated_conjecture,
    ( k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k2_xboole_0(esk3_0,esk4_0)) = k5_enumset1(X1,X1,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_57])).

cnf(c_0_128,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk3_0),k2_xboole_0(esk3_0,esk4_0)) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_69]),c_0_124]),c_0_83])).

cnf(c_0_129,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k3_enumset1(X3,X3,X3,X3,X3)) = k2_xboole_0(k4_xboole_0(X1,k3_enumset1(X3,X3,X3,X3,X3)),X2)
    | r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_108,c_0_125])).

cnf(c_0_130,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k3_enumset1(esk2_0,esk2_0,esk2_0,X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_57]),c_0_41]),c_0_69]),c_0_124]),c_0_83]),c_0_43]),c_0_41]),c_0_83])).

cnf(c_0_131,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk3_0),esk3_0),k2_xboole_0(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_128])).

cnf(c_0_132,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(esk3_0,esk4_0)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(esk3_0,esk4_0)),X2)
    | r2_hidden(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_129,c_0_57])).

cnf(c_0_133,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_57]),c_0_40])).

cnf(c_0_134,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,esk3_0) = k1_xboole_0
    | r2_hidden(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_58]),c_0_43]),c_0_30])).

fof(c_0_135,plain,(
    ! [X9,X10,X11] :
      ( ( r1_tarski(X9,esk1_3(X9,X10,X11))
        | ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X11,X10)
        | X10 = k2_xboole_0(X9,X11) )
      & ( r1_tarski(X11,esk1_3(X9,X10,X11))
        | ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X11,X10)
        | X10 = k2_xboole_0(X9,X11) )
      & ( ~ r1_tarski(X10,esk1_3(X9,X10,X11))
        | ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X11,X10)
        | X10 = k2_xboole_0(X9,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).

cnf(c_0_136,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,esk4_0) = k1_xboole_0
    | r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_133]),c_0_57])).

cnf(c_0_137,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,esk3_0) = k1_xboole_0
    | r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_134]),c_0_57])).

cnf(c_0_138,plain,
    ( r1_tarski(X1,esk1_3(X2,X3,X1))
    | X3 = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_135])).

cnf(c_0_139,plain,
    ( r1_tarski(X1,esk1_3(X1,X2,X3))
    | X2 = k2_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_135])).

cnf(c_0_140,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,esk4_0) = k1_xboole_0
    | k2_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_136]),c_0_88])])).

cnf(c_0_141,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,esk3_0) = k1_xboole_0
    | k2_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_137]),c_0_59])])).

cnf(c_0_142,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_143,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r1_tarski(X2,esk1_3(X1,X1,X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_138,c_0_84])).

cnf(c_0_144,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X1)
    | r1_tarski(X3,esk1_3(X3,k2_xboole_0(X1,X2),X1))
    | ~ r1_tarski(X3,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_59])).

cnf(c_0_145,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,X1),k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_55])).

cnf(c_0_146,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_103]),c_0_41]),c_0_55]),c_0_41]),c_0_55])).

cnf(c_0_147,plain,
    ( r1_tarski(k1_xboole_0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_114])).

cnf(c_0_148,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,esk3_0) = k1_xboole_0
    | k2_xboole_0(k1_xboole_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_142])).

cnf(c_0_149,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,esk1_3(X2,X1,X3))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_135])).

cnf(c_0_150,plain,
    ( k2_xboole_0(X1,X1) = X1
    | r1_tarski(X1,esk1_3(X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_143,c_0_84])).

cnf(c_0_151,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1)
    | r1_tarski(k2_xboole_0(k1_xboole_0,X2),esk1_3(k2_xboole_0(k1_xboole_0,X2),k2_xboole_0(X1,X2),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_145]),c_0_41]),c_0_146])).

cnf(c_0_152,plain,
    ( r1_tarski(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_59]),c_0_55])).

cnf(c_0_153,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_40]),c_0_41]),c_0_55]),c_0_41])).

cnf(c_0_154,negated_conjecture,
    ( k2_xboole_0(esk4_0,X1) = k2_xboole_0(k1_xboole_0,X1)
    | k2_xboole_0(k1_xboole_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_148]),c_0_146])).

cnf(c_0_155,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_150]),c_0_84])])).

cnf(c_0_156,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_58])).

cnf(c_0_157,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_151]),c_0_41]),c_0_146]),c_0_152]),c_0_145])])).

cnf(c_0_158,negated_conjecture,
    ( k2_xboole_0(X1,esk4_0) = k2_xboole_0(X1,k1_xboole_0)
    | k2_xboole_0(k1_xboole_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_148]),c_0_146]),c_0_146])).

cnf(c_0_159,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,esk3_0) = k1_xboole_0
    | k2_xboole_0(k1_xboole_0,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_154,c_0_155])).

cnf(c_0_160,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_161,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_156,c_0_157])).

cnf(c_0_162,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_159]),c_0_155]),c_0_160])).

cnf(c_0_163,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_162]),c_0_105]),c_0_115]),c_0_155]),c_0_105])).

cnf(c_0_164,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_165,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_162,c_0_163]),c_0_164]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 3.57/3.79  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 3.57/3.79  # and selection function SelectNegativeLiterals.
% 3.57/3.79  #
% 3.57/3.79  # Preprocessing time       : 0.027 s
% 3.57/3.79  
% 3.57/3.79  # Proof found!
% 3.57/3.79  # SZS status Theorem
% 3.57/3.79  # SZS output start CNFRefutation
% 3.57/3.79  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.57/3.79  fof(t82_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 3.57/3.79  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.57/3.79  fof(t44_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.57/3.79  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.57/3.79  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.57/3.79  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 3.57/3.79  fof(t37_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 3.57/3.79  fof(t87_enumset1, axiom, ![X1]:k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_enumset1)).
% 3.57/3.79  fof(l57_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 3.57/3.79  fof(t83_enumset1, axiom, ![X1, X2]:k3_enumset1(X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_enumset1)).
% 3.57/3.79  fof(t84_enumset1, axiom, ![X1, X2, X3]:k4_enumset1(X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_enumset1)).
% 3.57/3.79  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.57/3.79  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 3.57/3.79  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.57/3.79  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.57/3.79  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.57/3.79  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.57/3.79  fof(t87_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k2_xboole_0(k4_xboole_0(X3,X1),X2)=k4_xboole_0(k2_xboole_0(X3,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 3.57/3.79  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.57/3.79  fof(t14_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 3.57/3.79  fof(c_0_21, plain, ![X26]:((r1_xboole_0(X26,X26)|X26!=k1_xboole_0)&(X26=k1_xboole_0|~r1_xboole_0(X26,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 3.57/3.79  fof(c_0_22, plain, ![X31, X32]:r1_xboole_0(k4_xboole_0(X31,X32),k4_xboole_0(X32,X31)), inference(variable_rename,[status(thm)],[t82_xboole_1])).
% 3.57/3.79  fof(c_0_23, plain, ![X13, X14]:k2_xboole_0(X13,k4_xboole_0(X14,X13))=k2_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 3.57/3.79  cnf(c_0_24, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.57/3.79  cnf(c_0_25, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.57/3.79  fof(c_0_26, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t44_zfmisc_1])).
% 3.57/3.79  fof(c_0_27, plain, ![X21, X22]:k4_xboole_0(X21,k2_xboole_0(X21,X22))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 3.57/3.79  fof(c_0_28, plain, ![X23, X24, X25]:k2_xboole_0(k2_xboole_0(X23,X24),X25)=k2_xboole_0(X23,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 3.57/3.79  cnf(c_0_29, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.57/3.79  cnf(c_0_30, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 3.57/3.79  fof(c_0_31, plain, ![X27, X28]:k2_xboole_0(X27,k2_xboole_0(X27,X28))=k2_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 3.57/3.79  fof(c_0_32, plain, ![X61, X62]:((~r1_tarski(k1_tarski(X61),X62)|r2_hidden(X61,X62))&(~r2_hidden(X61,X62)|r1_tarski(k1_tarski(X61),X62))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).
% 3.57/3.79  fof(c_0_33, plain, ![X58]:k3_enumset1(X58,X58,X58,X58,X58)=k1_tarski(X58), inference(variable_rename,[status(thm)],[t87_enumset1])).
% 3.57/3.79  fof(c_0_34, negated_conjecture, (((k1_tarski(esk2_0)=k2_xboole_0(esk3_0,esk4_0)&esk3_0!=esk4_0)&esk3_0!=k1_xboole_0)&esk4_0!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 3.57/3.79  fof(c_0_35, plain, ![X36, X37, X38, X39, X40]:k3_enumset1(X36,X37,X38,X39,X40)=k2_xboole_0(k1_enumset1(X36,X37,X38),k2_tarski(X39,X40)), inference(variable_rename,[status(thm)],[l57_enumset1])).
% 3.57/3.79  fof(c_0_36, plain, ![X53, X54]:k3_enumset1(X53,X53,X53,X53,X54)=k2_tarski(X53,X54), inference(variable_rename,[status(thm)],[t83_enumset1])).
% 3.57/3.79  fof(c_0_37, plain, ![X55, X56, X57]:k4_enumset1(X55,X55,X55,X55,X56,X57)=k1_enumset1(X55,X56,X57), inference(variable_rename,[status(thm)],[t84_enumset1])).
% 3.57/3.79  fof(c_0_38, plain, ![X47, X48, X49, X50, X51, X52]:k5_enumset1(X47,X47,X48,X49,X50,X51,X52)=k4_enumset1(X47,X48,X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 3.57/3.79  fof(c_0_39, plain, ![X41, X42, X43, X44, X45, X46]:k4_enumset1(X41,X42,X43,X44,X45,X46)=k2_xboole_0(k1_tarski(X41),k3_enumset1(X42,X43,X44,X45,X46)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 3.57/3.79  cnf(c_0_40, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.57/3.79  cnf(c_0_41, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.57/3.79  cnf(c_0_42, plain, (k2_xboole_0(X1,k1_xboole_0)=k2_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 3.57/3.79  cnf(c_0_43, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.57/3.79  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.57/3.79  cnf(c_0_45, plain, (k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.57/3.79  cnf(c_0_46, negated_conjecture, (k1_tarski(esk2_0)=k2_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.57/3.79  fof(c_0_47, plain, ![X15, X16, X17]:k4_xboole_0(k4_xboole_0(X15,X16),X17)=k4_xboole_0(X15,k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 3.57/3.79  fof(c_0_48, plain, ![X29, X30]:r1_tarski(X29,k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 3.57/3.79  cnf(c_0_49, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 3.57/3.79  cnf(c_0_50, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.57/3.79  cnf(c_0_51, plain, (k4_enumset1(X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 3.57/3.79  cnf(c_0_52, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.57/3.79  cnf(c_0_53, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 3.57/3.79  cnf(c_0_54, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X2,X3)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 3.57/3.79  cnf(c_0_55, plain, (k2_xboole_0(X1,k2_xboole_0(k1_xboole_0,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_41]), c_0_43])).
% 3.57/3.79  cnf(c_0_56, plain, (r2_hidden(X1,X2)|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 3.57/3.79  cnf(c_0_57, negated_conjecture, (k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_46, c_0_45])).
% 3.57/3.79  cnf(c_0_58, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 3.57/3.79  cnf(c_0_59, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 3.57/3.79  cnf(c_0_60, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52])).
% 3.57/3.79  cnf(c_0_61, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_45]), c_0_52])).
% 3.57/3.79  cnf(c_0_62, plain, (k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 3.57/3.79  cnf(c_0_63, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.57/3.79  cnf(c_0_64, negated_conjecture, (r2_hidden(esk2_0,X1)|~r1_tarski(k2_xboole_0(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 3.57/3.79  cnf(c_0_65, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_30]), c_0_29])).
% 3.57/3.79  fof(c_0_66, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.57/3.79  cnf(c_0_67, plain, (r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k3_enumset1(X1,X2,X3,X4,X5))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 3.57/3.79  cnf(c_0_68, negated_conjecture, (k5_enumset1(esk2_0,esk2_0,X1,X2,X3,X4,X5)=k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k3_enumset1(X1,X2,X3,X4,X5)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_57]), c_0_41])).
% 3.57/3.79  cnf(c_0_69, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))=k2_xboole_0(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_40]), c_0_41]), c_0_41])).
% 3.57/3.79  cnf(c_0_70, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,k1_xboole_0)))=k2_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_62]), c_0_41]), c_0_41])).
% 3.57/3.79  cnf(c_0_71, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_63, c_0_45])).
% 3.57/3.79  cnf(c_0_72, negated_conjecture, (r2_hidden(esk2_0,k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_59]), c_0_41])).
% 3.57/3.79  fof(c_0_73, plain, ![X18, X19, X20]:(~r1_tarski(k4_xboole_0(X18,X19),X20)|r1_tarski(X18,k2_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 3.57/3.79  cnf(c_0_74, plain, (k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_55])).
% 3.57/3.79  cnf(c_0_75, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 3.57/3.79  cnf(c_0_76, negated_conjecture, (r1_tarski(k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k1_xboole_0)),k2_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_57]), c_0_68]), c_0_57]), c_0_69]), c_0_70])).
% 3.57/3.79  cnf(c_0_77, negated_conjecture, (r1_tarski(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_57])).
% 3.57/3.79  cnf(c_0_78, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_66])).
% 3.57/3.79  cnf(c_0_79, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 3.57/3.79  cnf(c_0_80, plain, (k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_29]), c_0_41])).
% 3.57/3.79  cnf(c_0_81, plain, (k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_42])).
% 3.57/3.79  cnf(c_0_82, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,k2_xboole_0(X1,k1_xboole_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_69])).
% 3.57/3.79  cnf(c_0_83, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k1_xboole_0))=k2_xboole_0(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])])).
% 3.57/3.79  cnf(c_0_84, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_78])).
% 3.57/3.79  cnf(c_0_85, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_59]), c_0_80])).
% 3.57/3.79  cnf(c_0_86, plain, (r1_tarski(k2_xboole_0(k1_xboole_0,X1),k2_xboole_0(X1,X2))|~r1_tarski(k1_xboole_0,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_81]), c_0_41]), c_0_55])).
% 3.57/3.79  cnf(c_0_87, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk4_0,esk3_0),k2_xboole_0(esk3_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 3.57/3.79  cnf(c_0_88, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_84]), c_0_29])).
% 3.57/3.79  cnf(c_0_89, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,k2_xboole_0(X2,X3))))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_41]), c_0_41]), c_0_41])).
% 3.57/3.79  cnf(c_0_90, negated_conjecture, (r2_hidden(esk2_0,k2_xboole_0(X1,k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_85]), c_0_41])).
% 3.57/3.79  cnf(c_0_91, plain, (r1_tarski(k2_xboole_0(k1_xboole_0,X1),k2_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_86, c_0_84])).
% 3.57/3.79  cnf(c_0_92, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)))=k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_87]), c_0_41]), c_0_55]), c_0_41]), c_0_41]), c_0_43])).
% 3.57/3.79  cnf(c_0_93, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_29, c_0_58])).
% 3.57/3.79  cnf(c_0_94, plain, (r1_tarski(k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))),k2_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 3.57/3.79  cnf(c_0_95, negated_conjecture, (r2_hidden(esk2_0,k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_90, c_0_89])).
% 3.57/3.79  cnf(c_0_96, plain, (r1_tarski(k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X1,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_69]), c_0_41]), c_0_55])).
% 3.57/3.79  cnf(c_0_97, plain, (k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k3_enumset1(X1,X2,X3,X4,X5))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_60])).
% 3.57/3.79  cnf(c_0_98, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1)))=k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_89, c_0_92])).
% 3.57/3.79  cnf(c_0_99, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=k2_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_93, c_0_65])).
% 3.57/3.79  cnf(c_0_100, negated_conjecture, (r1_tarski(k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,k1_xboole_0)),k2_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_83]), c_0_69])).
% 3.57/3.79  cnf(c_0_101, negated_conjecture, (r1_tarski(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_95]), c_0_57])).
% 3.57/3.79  fof(c_0_102, plain, ![X33, X34, X35]:(~r1_xboole_0(X33,X34)|k2_xboole_0(k4_xboole_0(X35,X33),X34)=k4_xboole_0(k2_xboole_0(X35,X34),X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_xboole_1])])).
% 3.57/3.79  cnf(c_0_103, plain, (k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0))=k2_xboole_0(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_96]), c_0_88])])).
% 3.57/3.79  cnf(c_0_104, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k1_xboole_0)),k2_xboole_0(esk3_0,esk4_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_57]), c_0_68]), c_0_57]), c_0_69]), c_0_70])).
% 3.57/3.79  cnf(c_0_105, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_29]), c_0_55])).
% 3.57/3.79  cnf(c_0_106, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,k4_xboole_0(esk4_0,X1)))=k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_70])).
% 3.57/3.79  cnf(c_0_107, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,k1_xboole_0))=k2_xboole_0(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_100]), c_0_101])])).
% 3.57/3.79  cnf(c_0_108, plain, (k2_xboole_0(k4_xboole_0(X3,X1),X2)=k4_xboole_0(k2_xboole_0(X3,X2),X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 3.57/3.79  cnf(c_0_109, plain, (k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0)=k2_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_103]), c_0_103])).
% 3.57/3.79  cnf(c_0_110, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,k1_xboole_0)),esk3_0))=k2_xboole_0(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_93, c_0_104])).
% 3.57/3.79  cnf(c_0_111, plain, (r1_tarski(k4_xboole_0(X1,k1_xboole_0),k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_88, c_0_105])).
% 3.57/3.79  cnf(c_0_112, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,k4_xboole_0(esk4_0,X1)))=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_106, c_0_107])).
% 3.57/3.79  cnf(c_0_113, plain, (k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X3,X2))=k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_108, c_0_25])).
% 3.57/3.79  cnf(c_0_114, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_40]), c_0_41]), c_0_40])).
% 3.57/3.79  cnf(c_0_115, plain, (k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),X2)=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_109]), c_0_41]), c_0_55]), c_0_55])).
% 3.57/3.79  fof(c_0_116, plain, ![X59, X60]:(r2_hidden(X59,X60)|r1_xboole_0(k1_tarski(X59),X60)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 3.57/3.79  cnf(c_0_117, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk3_0))=k2_xboole_0(esk4_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_110, c_0_83])).
% 3.57/3.79  cnf(c_0_118, plain, (k4_xboole_0(X1,k1_xboole_0)=k2_xboole_0(X2,X1)|~r1_tarski(k2_xboole_0(X2,X1),k4_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_75, c_0_111])).
% 3.57/3.79  cnf(c_0_119, negated_conjecture, (k2_xboole_0(X1,k2_xboole_0(esk4_0,k2_xboole_0(X1,k2_xboole_0(esk3_0,esk4_0))))=k2_xboole_0(X1,k2_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_89, c_0_112])).
% 3.57/3.79  cnf(c_0_120, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_105]), c_0_115]), c_0_105])).
% 3.57/3.79  cnf(c_0_121, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_116])).
% 3.57/3.79  cnf(c_0_122, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk3_0),X1))=k2_xboole_0(esk4_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_117]), c_0_41]), c_0_55])).
% 3.57/3.79  cnf(c_0_123, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(X1,k2_xboole_0(esk3_0,esk4_0)))=k2_xboole_0(X1,k2_xboole_0(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_120]), c_0_120]), c_0_88])])).
% 3.57/3.79  cnf(c_0_124, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))=k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_107]), c_0_41]), c_0_41]), c_0_55])).
% 3.57/3.79  cnf(c_0_125, plain, (r2_hidden(X1,X2)|r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[c_0_121, c_0_45])).
% 3.57/3.79  cnf(c_0_126, plain, (k4_xboole_0(k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k1_xboole_0),k3_enumset1(X1,X2,X3,X4,X5))=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_60])).
% 3.57/3.79  cnf(c_0_127, negated_conjecture, (k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k2_xboole_0(esk3_0,esk4_0))=k5_enumset1(X1,X1,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_61, c_0_57])).
% 3.57/3.79  cnf(c_0_128, negated_conjecture, (k2_xboole_0(k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk3_0),k2_xboole_0(esk3_0,esk4_0))=k2_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_69]), c_0_124]), c_0_83])).
% 3.57/3.79  cnf(c_0_129, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k3_enumset1(X3,X3,X3,X3,X3))=k2_xboole_0(k4_xboole_0(X1,k3_enumset1(X3,X3,X3,X3,X3)),X2)|r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_108, c_0_125])).
% 3.57/3.79  cnf(c_0_130, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),k3_enumset1(esk2_0,esk2_0,esk2_0,X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_57]), c_0_41]), c_0_69]), c_0_124]), c_0_83]), c_0_43]), c_0_41]), c_0_83])).
% 3.57/3.79  cnf(c_0_131, negated_conjecture, (k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk3_0),esk3_0),k2_xboole_0(esk3_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_128])).
% 3.57/3.79  cnf(c_0_132, negated_conjecture, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(esk3_0,esk4_0))=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(esk3_0,esk4_0)),X2)|r2_hidden(esk2_0,X2)), inference(spm,[status(thm)],[c_0_129, c_0_57])).
% 3.57/3.79  cnf(c_0_133, negated_conjecture, (k2_xboole_0(k1_xboole_0,esk4_0)=k1_xboole_0|r2_hidden(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_57]), c_0_40])).
% 3.57/3.79  cnf(c_0_134, negated_conjecture, (k2_xboole_0(k1_xboole_0,esk3_0)=k1_xboole_0|r2_hidden(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_58]), c_0_43]), c_0_30])).
% 3.57/3.79  fof(c_0_135, plain, ![X9, X10, X11]:(((r1_tarski(X9,esk1_3(X9,X10,X11))|(~r1_tarski(X9,X10)|~r1_tarski(X11,X10))|X10=k2_xboole_0(X9,X11))&(r1_tarski(X11,esk1_3(X9,X10,X11))|(~r1_tarski(X9,X10)|~r1_tarski(X11,X10))|X10=k2_xboole_0(X9,X11)))&(~r1_tarski(X10,esk1_3(X9,X10,X11))|(~r1_tarski(X9,X10)|~r1_tarski(X11,X10))|X10=k2_xboole_0(X9,X11))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).
% 3.57/3.79  cnf(c_0_136, negated_conjecture, (k2_xboole_0(k1_xboole_0,esk4_0)=k1_xboole_0|r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_133]), c_0_57])).
% 3.57/3.79  cnf(c_0_137, negated_conjecture, (k2_xboole_0(k1_xboole_0,esk3_0)=k1_xboole_0|r1_tarski(k2_xboole_0(esk3_0,esk4_0),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_134]), c_0_57])).
% 3.57/3.79  cnf(c_0_138, plain, (r1_tarski(X1,esk1_3(X2,X3,X1))|X3=k2_xboole_0(X2,X1)|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_135])).
% 3.57/3.79  cnf(c_0_139, plain, (r1_tarski(X1,esk1_3(X1,X2,X3))|X2=k2_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_135])).
% 3.57/3.79  cnf(c_0_140, negated_conjecture, (k2_xboole_0(k1_xboole_0,esk4_0)=k1_xboole_0|k2_xboole_0(esk3_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_136]), c_0_88])])).
% 3.57/3.79  cnf(c_0_141, negated_conjecture, (k2_xboole_0(k1_xboole_0,esk3_0)=k1_xboole_0|k2_xboole_0(esk3_0,esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_137]), c_0_59])])).
% 3.57/3.79  cnf(c_0_142, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.57/3.79  cnf(c_0_143, plain, (k2_xboole_0(X1,X2)=X1|r1_tarski(X2,esk1_3(X1,X1,X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_138, c_0_84])).
% 3.57/3.79  cnf(c_0_144, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X3,X1)|r1_tarski(X3,esk1_3(X3,k2_xboole_0(X1,X2),X1))|~r1_tarski(X3,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_139, c_0_59])).
% 3.57/3.79  cnf(c_0_145, plain, (r1_tarski(k2_xboole_0(k1_xboole_0,X1),k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_88, c_0_55])).
% 3.57/3.79  cnf(c_0_146, plain, (k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_103]), c_0_41]), c_0_55]), c_0_41]), c_0_55])).
% 3.57/3.79  cnf(c_0_147, plain, (r1_tarski(k1_xboole_0,k2_xboole_0(X1,X2))|~r1_tarski(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_79, c_0_114])).
% 3.57/3.79  cnf(c_0_148, negated_conjecture, (k2_xboole_0(k1_xboole_0,esk3_0)=k1_xboole_0|k2_xboole_0(k1_xboole_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_142])).
% 3.57/3.79  cnf(c_0_149, plain, (X1=k2_xboole_0(X2,X3)|~r1_tarski(X1,esk1_3(X2,X1,X3))|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_135])).
% 3.57/3.79  cnf(c_0_150, plain, (k2_xboole_0(X1,X1)=X1|r1_tarski(X1,esk1_3(X1,X1,X1))), inference(spm,[status(thm)],[c_0_143, c_0_84])).
% 3.57/3.79  cnf(c_0_151, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)|r1_tarski(k2_xboole_0(k1_xboole_0,X2),esk1_3(k2_xboole_0(k1_xboole_0,X2),k2_xboole_0(X1,X2),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_145]), c_0_41]), c_0_146])).
% 3.57/3.79  cnf(c_0_152, plain, (r1_tarski(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_59]), c_0_55])).
% 3.57/3.79  cnf(c_0_153, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_40]), c_0_41]), c_0_55]), c_0_41])).
% 3.57/3.79  cnf(c_0_154, negated_conjecture, (k2_xboole_0(esk4_0,X1)=k2_xboole_0(k1_xboole_0,X1)|k2_xboole_0(k1_xboole_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_148]), c_0_146])).
% 3.57/3.79  cnf(c_0_155, plain, (k2_xboole_0(X1,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_150]), c_0_84])])).
% 3.57/3.79  cnf(c_0_156, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3)))=k2_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_99, c_0_58])).
% 3.57/3.79  cnf(c_0_157, plain, (k2_xboole_0(k1_xboole_0,X1)=k2_xboole_0(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_151]), c_0_41]), c_0_146]), c_0_152]), c_0_145])])).
% 3.57/3.79  cnf(c_0_158, negated_conjecture, (k2_xboole_0(X1,esk4_0)=k2_xboole_0(X1,k1_xboole_0)|k2_xboole_0(k1_xboole_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_148]), c_0_146]), c_0_146])).
% 3.57/3.79  cnf(c_0_159, negated_conjecture, (k2_xboole_0(k1_xboole_0,esk3_0)=k1_xboole_0|k2_xboole_0(k1_xboole_0,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_154, c_0_155])).
% 3.57/3.79  cnf(c_0_160, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.57/3.79  cnf(c_0_161, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3)))=k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_156, c_0_157])).
% 3.57/3.79  cnf(c_0_162, negated_conjecture, (k2_xboole_0(k1_xboole_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_159]), c_0_155]), c_0_160])).
% 3.57/3.79  cnf(c_0_163, negated_conjecture, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_162]), c_0_105]), c_0_115]), c_0_155]), c_0_105])).
% 3.57/3.79  cnf(c_0_164, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.57/3.79  cnf(c_0_165, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_162, c_0_163]), c_0_164]), ['proof']).
% 3.57/3.79  # SZS output end CNFRefutation
% 3.57/3.79  # Proof object total steps             : 166
% 3.57/3.79  # Proof object clause steps            : 123
% 3.57/3.79  # Proof object formula steps           : 43
% 3.57/3.79  # Proof object conjectures             : 49
% 3.57/3.79  # Proof object clause conjectures      : 46
% 3.57/3.79  # Proof object formula conjectures     : 3
% 3.57/3.79  # Proof object initial clauses used    : 28
% 3.57/3.79  # Proof object initial formulas used   : 21
% 3.57/3.79  # Proof object generating inferences   : 84
% 3.57/3.79  # Proof object simplifying inferences  : 125
% 3.57/3.79  # Training examples: 0 positive, 0 negative
% 3.57/3.79  # Parsed axioms                        : 21
% 3.57/3.79  # Removed by relevancy pruning/SinE    : 0
% 3.57/3.79  # Initial clauses                      : 30
% 3.57/3.79  # Removed in clause preprocessing      : 4
% 3.57/3.79  # Initial clauses in saturation        : 26
% 3.57/3.79  # Processed clauses                    : 15389
% 3.57/3.79  # ...of these trivial                  : 623
% 3.57/3.79  # ...subsumed                          : 12813
% 3.57/3.79  # ...remaining for further processing  : 1953
% 3.57/3.79  # Other redundant clauses eliminated   : 2
% 3.57/3.79  # Clauses deleted for lack of memory   : 0
% 3.57/3.79  # Backward-subsumed                    : 135
% 3.57/3.79  # Backward-rewritten                   : 1260
% 3.57/3.79  # Generated clauses                    : 475034
% 3.57/3.79  # ...of the previous two non-trivial   : 323614
% 3.57/3.79  # Contextual simplify-reflections      : 2
% 3.57/3.79  # Paramodulations                      : 475027
% 3.57/3.79  # Factorizations                       : 4
% 3.57/3.79  # Equation resolutions                 : 3
% 3.57/3.79  # Propositional unsat checks           : 0
% 3.57/3.79  #    Propositional check models        : 0
% 3.57/3.79  #    Propositional check unsatisfiable : 0
% 3.57/3.79  #    Propositional clauses             : 0
% 3.57/3.79  #    Propositional clauses after purity: 0
% 3.57/3.79  #    Propositional unsat core size     : 0
% 3.57/3.79  #    Propositional preprocessing time  : 0.000
% 3.57/3.79  #    Propositional encoding time       : 0.000
% 3.57/3.79  #    Propositional solver time         : 0.000
% 3.57/3.79  #    Success case prop preproc time    : 0.000
% 3.57/3.79  #    Success case prop encoding time   : 0.000
% 3.57/3.79  #    Success case prop solver time     : 0.000
% 3.57/3.79  # Current number of processed clauses  : 556
% 3.57/3.79  #    Positive orientable unit clauses  : 347
% 3.57/3.79  #    Positive unorientable unit clauses: 12
% 3.57/3.79  #    Negative unit clauses             : 4
% 3.57/3.79  #    Non-unit-clauses                  : 193
% 3.57/3.79  # Current number of unprocessed clauses: 305997
% 3.57/3.79  # ...number of literals in the above   : 596106
% 3.57/3.79  # Current number of archived formulas  : 0
% 3.57/3.79  # Current number of archived clauses   : 1399
% 3.57/3.79  # Clause-clause subsumption calls (NU) : 189975
% 3.57/3.79  # Rec. Clause-clause subsumption calls : 151240
% 3.57/3.79  # Non-unit clause-clause subsumptions  : 12058
% 3.57/3.79  # Unit Clause-clause subsumption calls : 11447
% 3.57/3.79  # Rewrite failures with RHS unbound    : 0
% 3.57/3.79  # BW rewrite match attempts            : 7687
% 3.57/3.79  # BW rewrite match successes           : 1428
% 3.57/3.79  # Condensation attempts                : 0
% 3.57/3.79  # Condensation successes               : 0
% 3.57/3.79  # Termbank termtop insertions          : 7541505
% 3.57/3.80  
% 3.57/3.80  # -------------------------------------------------
% 3.57/3.80  # User time                : 3.287 s
% 3.57/3.80  # System time              : 0.173 s
% 3.57/3.80  # Total time               : 3.460 s
% 3.57/3.80  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
