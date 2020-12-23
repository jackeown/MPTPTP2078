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
% DateTime   : Thu Dec  3 10:42:56 EST 2020

% Result     : Theorem 4.44s
% Output     : CNFRefutation 4.44s
% Verified   : 
% Statistics : Number of formulae       :  139 (76132 expanded)
%              Number of clauses        :   98 (33375 expanded)
%              Number of leaves         :   20 (21328 expanded)
%              Depth                    :   25
%              Number of atoms          :  331 (93551 expanded)
%              Number of equality atoms :  181 (75169 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t70_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).

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

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(t60_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,X2)
     => ( ( r2_hidden(X3,X2)
          & X1 != X3 )
        | k3_xboole_0(k2_tarski(X1,X3),X2) = k1_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(c_0_20,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k3_xboole_0(X27,X28) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_21,plain,(
    ! [X29] : r1_tarski(k1_xboole_0,X29) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_22,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k4_xboole_0(X30,X31)) = k3_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_23,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_24,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_31,plain,(
    ! [X32] : k5_xboole_0(X32,k1_xboole_0) = X32 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_32,plain,(
    ! [X18] : k3_xboole_0(X18,X18) = X18 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_33,plain,(
    ! [X33,X34,X35] : k5_xboole_0(k5_xboole_0(X33,X34),X35) = k5_xboole_0(X33,k5_xboole_0(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_28])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
      <=> ( ~ r2_hidden(X1,X3)
          & ( r2_hidden(X2,X3)
            | X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t70_zfmisc_1])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])).

fof(c_0_41,negated_conjecture,
    ( ( ~ r2_hidden(esk4_0,esk5_0)
      | r2_hidden(esk3_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0) )
    & ( esk3_0 != esk4_0
      | r2_hidden(esk3_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0) )
    & ( ~ r2_hidden(esk3_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_tarski(esk3_0) )
    & ( r2_hidden(esk4_0,esk5_0)
      | esk3_0 = esk4_0
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_tarski(esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])])).

fof(c_0_42,plain,(
    ! [X47] : k2_tarski(X47,X47) = k1_tarski(X47) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_43,plain,(
    ! [X48,X49] : k1_enumset1(X48,X48,X49) = k2_tarski(X48,X49) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_44,plain,(
    ! [X50,X51,X52] : k2_enumset1(X50,X50,X51,X52) = k1_enumset1(X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_45,plain,(
    ! [X53,X54,X55,X56] : k3_enumset1(X53,X53,X54,X55,X56) = k2_enumset1(X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_46,plain,(
    ! [X57,X58,X59,X60,X61] : k4_enumset1(X57,X57,X58,X59,X60,X61) = k3_enumset1(X57,X58,X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_47,plain,(
    ! [X62,X63,X64,X65,X66,X67] : k5_enumset1(X62,X62,X63,X64,X65,X66,X67) = k4_enumset1(X62,X63,X64,X65,X66,X67) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | esk3_0 = esk4_0
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_56,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42,X43,X44,X45] :
      ( ( ~ r2_hidden(X40,X39)
        | X40 = X36
        | X40 = X37
        | X40 = X38
        | X39 != k1_enumset1(X36,X37,X38) )
      & ( X41 != X36
        | r2_hidden(X41,X39)
        | X39 != k1_enumset1(X36,X37,X38) )
      & ( X41 != X37
        | r2_hidden(X41,X39)
        | X39 != k1_enumset1(X36,X37,X38) )
      & ( X41 != X38
        | r2_hidden(X41,X39)
        | X39 != k1_enumset1(X36,X37,X38) )
      & ( esk2_4(X42,X43,X44,X45) != X42
        | ~ r2_hidden(esk2_4(X42,X43,X44,X45),X45)
        | X45 = k1_enumset1(X42,X43,X44) )
      & ( esk2_4(X42,X43,X44,X45) != X43
        | ~ r2_hidden(esk2_4(X42,X43,X44,X45),X45)
        | X45 = k1_enumset1(X42,X43,X44) )
      & ( esk2_4(X42,X43,X44,X45) != X44
        | ~ r2_hidden(esk2_4(X42,X43,X44,X45),X45)
        | X45 = k1_enumset1(X42,X43,X44) )
      & ( r2_hidden(esk2_4(X42,X43,X44,X45),X45)
        | esk2_4(X42,X43,X44,X45) = X42
        | esk2_4(X42,X43,X44,X45) = X43
        | esk2_4(X42,X43,X44,X45) = X44
        | X45 = k1_enumset1(X42,X43,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_40]),c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( esk4_0 = esk3_0
    | k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_51]),c_0_28]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_55])).

fof(c_0_59,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X15)
        | X16 = k4_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X15)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_48,c_0_57])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_63,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_29])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_65,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r2_hidden(X19,X20)
        | ~ r2_hidden(X19,X21)
        | ~ r2_hidden(X19,k5_xboole_0(X20,X21)) )
      & ( r2_hidden(X19,X20)
        | r2_hidden(X19,X21)
        | ~ r2_hidden(X19,k5_xboole_0(X20,X21)) )
      & ( ~ r2_hidden(X19,X20)
        | r2_hidden(X19,X21)
        | r2_hidden(X19,k5_xboole_0(X20,X21)) )
      & ( ~ r2_hidden(X19,X21)
        | r2_hidden(X19,X20)
        | r2_hidden(X19,k5_xboole_0(X20,X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_52]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_36])).

cnf(c_0_68,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k3_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))
    | esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_63])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_64,c_0_28])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0)
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_71,plain,(
    ! [X24,X25,X26] : k5_xboole_0(k3_xboole_0(X24,X25),k3_xboole_0(X26,X25)) = k3_xboole_0(k5_xboole_0(X24,X26),X25) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

cnf(c_0_72,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_66])])).

cnf(c_0_75,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | esk3_0 != esk4_0
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_50]),c_0_51]),c_0_51]),c_0_28]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_55])).

cnf(c_0_80,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_67])).

cnf(c_0_82,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k5_enumset1(X3,X3,X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_52]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X4,X1)))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) = k3_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))
    | esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_75])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_34])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | esk4_0 != esk3_0
    | k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) != k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_50]),c_0_51]),c_0_51]),c_0_28]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_55])).

fof(c_0_87,plain,(
    ! [X74,X75,X76] :
      ( ( r2_hidden(X76,X75)
        | k3_xboole_0(k2_tarski(X74,X76),X75) = k1_tarski(X74)
        | ~ r2_hidden(X74,X75) )
      & ( X74 != X76
        | k3_xboole_0(k2_tarski(X74,X76),X75) = k1_tarski(X74)
        | ~ r2_hidden(X74,X75) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X4,X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_52]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) != k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_79,c_0_29])).

cnf(c_0_90,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_37]),c_0_29]),c_0_81])).

cnf(c_0_91,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k5_enumset1(X4,X4,X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk4_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) != k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk4_0 != esk3_0 ),
    inference(rw,[status(thm)],[c_0_86,c_0_29])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,X2)
    | k3_xboole_0(k2_tarski(X3,X1),X2) = k1_tarski(X3)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_88])])).

cnf(c_0_96,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) != k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) != k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk4_0 != esk3_0 ),
    inference(rw,[status(thm)],[c_0_93,c_0_90])).

cnf(c_0_100,plain,
    ( k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X1),X2) = k5_enumset1(X3,X3,X3,X3,X3,X3,X3)
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_55]),c_0_55])).

cnf(c_0_101,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X1,X4)))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_95])).

cnf(c_0_102,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_96,c_0_28])).

cnf(c_0_103,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) != k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])).

cnf(c_0_105,plain,
    ( k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(X3,k5_enumset1(X4,X4,X4,X4,X4,X1,X5))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X2,k5_xboole_0(X3,k5_enumset1(X4,X4,X4,X4,X4,X1,X5)))
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_106,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_102])).

cnf(c_0_107,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_29])).

cnf(c_0_108,negated_conjecture,
    ( esk4_0 = esk3_0
    | ~ r2_hidden(esk4_0,k5_xboole_0(X1,esk5_0))
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_98])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))
    | r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_110,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_39]),c_0_81]),c_0_61]),c_0_74])])).

cnf(c_0_112,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_107]),c_0_107]),c_0_81]),c_0_107]),c_0_39]),c_0_40]),c_0_36])).

cnf(c_0_113,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_tarski(esk3_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_114,negated_conjecture,
    ( esk4_0 = esk3_0
    | ~ r2_hidden(esk3_0,k3_xboole_0(X1,k5_xboole_0(esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_115,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X1,X2))) = k3_xboole_0(k5_xboole_0(X1,X3),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_112]),c_0_90])).

cnf(c_0_116,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_50]),c_0_51]),c_0_51]),c_0_28]),c_0_52]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_55]),c_0_55]),c_0_55])).

cnf(c_0_117,plain,
    ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_118,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_119,negated_conjecture,
    ( esk4_0 = esk3_0
    | ~ r2_hidden(esk3_0,k3_xboole_0(k5_xboole_0(X1,esk5_0),k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_120,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_112,c_0_29])).

cnf(c_0_121,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_116,c_0_29])).

cnf(c_0_122,plain,
    ( k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),X3) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_55]),c_0_55])).

cnf(c_0_123,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X2,X2,X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_52]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_124,negated_conjecture,
    ( esk4_0 = esk3_0
    | ~ r2_hidden(esk3_0,k3_xboole_0(k5_xboole_0(X1,esk5_0),k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_125,negated_conjecture,
    ( k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_121,c_0_90])).

cnf(c_0_126,plain,
    ( k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_122])).

cnf(c_0_127,plain,
    ( r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_123])])).

cnf(c_0_128,negated_conjecture,
    ( esk4_0 = esk3_0
    | ~ r2_hidden(esk3_0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_124,c_0_29])).

cnf(c_0_129,negated_conjecture,
    ( k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk4_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_125,c_0_111])).

cnf(c_0_130,plain,
    ( k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X2,X3)) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_131,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X3,X4)))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_127])).

cnf(c_0_132,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_39]),c_0_81]),c_0_61]),c_0_130]),c_0_127])])).

cnf(c_0_133,plain,
    ( k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X3,X4))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_126,c_0_131])).

cnf(c_0_134,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_132]),c_0_132]),c_0_133])).

cnf(c_0_135,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k3_xboole_0(X1,k5_xboole_0(esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_134])).

cnf(c_0_136,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k3_xboole_0(k5_xboole_0(X1,esk5_0),k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_135,c_0_115])).

cnf(c_0_137,negated_conjecture,
    ( k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_132]),c_0_132]),c_0_134])])).

cnf(c_0_138,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_81]),c_0_29]),c_0_137]),c_0_127])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 4.44/4.62  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 4.44/4.62  # and selection function GSelectMinInfpos.
% 4.44/4.62  #
% 4.44/4.62  # Preprocessing time       : 0.028 s
% 4.44/4.62  # Presaturation interreduction done
% 4.44/4.62  
% 4.44/4.62  # Proof found!
% 4.44/4.62  # SZS status Theorem
% 4.44/4.62  # SZS output start CNFRefutation
% 4.44/4.62  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.44/4.62  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.44/4.62  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.44/4.62  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.44/4.62  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.44/4.62  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.44/4.62  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.44/4.62  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.44/4.62  fof(t70_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)<=>(~(r2_hidden(X1,X3))&(r2_hidden(X2,X3)|X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_zfmisc_1)).
% 4.44/4.62  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.44/4.62  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.44/4.62  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.44/4.62  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.44/4.62  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 4.44/4.62  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 4.44/4.62  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.44/4.62  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.44/4.62  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 4.44/4.62  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 4.44/4.62  fof(t60_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,X2)=>((r2_hidden(X3,X2)&X1!=X3)|k3_xboole_0(k2_tarski(X1,X3),X2)=k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 4.44/4.62  fof(c_0_20, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k3_xboole_0(X27,X28)=X27), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 4.44/4.62  fof(c_0_21, plain, ![X29]:r1_tarski(k1_xboole_0,X29), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 4.44/4.62  fof(c_0_22, plain, ![X30, X31]:k4_xboole_0(X30,k4_xboole_0(X30,X31))=k3_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 4.44/4.62  fof(c_0_23, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 4.44/4.62  fof(c_0_24, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 4.44/4.62  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.44/4.62  cnf(c_0_26, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.44/4.62  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.44/4.62  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.44/4.62  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.44/4.62  cnf(c_0_30, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 4.44/4.62  fof(c_0_31, plain, ![X32]:k5_xboole_0(X32,k1_xboole_0)=X32, inference(variable_rename,[status(thm)],[t5_boole])).
% 4.44/4.62  fof(c_0_32, plain, ![X18]:k3_xboole_0(X18,X18)=X18, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 4.44/4.62  fof(c_0_33, plain, ![X33, X34, X35]:k5_xboole_0(k5_xboole_0(X33,X34),X35)=k5_xboole_0(X33,k5_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 4.44/4.62  cnf(c_0_34, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_28])).
% 4.44/4.62  cnf(c_0_35, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 4.44/4.62  cnf(c_0_36, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 4.44/4.62  cnf(c_0_37, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.44/4.62  fof(c_0_38, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)<=>(~(r2_hidden(X1,X3))&(r2_hidden(X2,X3)|X1=X2)))), inference(assume_negation,[status(cth)],[t70_zfmisc_1])).
% 4.44/4.62  cnf(c_0_39, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.44/4.62  cnf(c_0_40, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])).
% 4.44/4.62  fof(c_0_41, negated_conjecture, (((~r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0))&(esk3_0!=esk4_0|r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0)))&((~r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_tarski(esk3_0))&(r2_hidden(esk4_0,esk5_0)|esk3_0=esk4_0|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_tarski(esk3_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])])).
% 4.44/4.62  fof(c_0_42, plain, ![X47]:k2_tarski(X47,X47)=k1_tarski(X47), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 4.44/4.62  fof(c_0_43, plain, ![X48, X49]:k1_enumset1(X48,X48,X49)=k2_tarski(X48,X49), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 4.44/4.62  fof(c_0_44, plain, ![X50, X51, X52]:k2_enumset1(X50,X50,X51,X52)=k1_enumset1(X50,X51,X52), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 4.44/4.62  fof(c_0_45, plain, ![X53, X54, X55, X56]:k3_enumset1(X53,X53,X54,X55,X56)=k2_enumset1(X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 4.44/4.62  fof(c_0_46, plain, ![X57, X58, X59, X60, X61]:k4_enumset1(X57,X57,X58,X59,X60,X61)=k3_enumset1(X57,X58,X59,X60,X61), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 4.44/4.62  fof(c_0_47, plain, ![X62, X63, X64, X65, X66, X67]:k5_enumset1(X62,X62,X63,X64,X65,X66,X67)=k4_enumset1(X62,X63,X64,X65,X66,X67), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 4.44/4.62  cnf(c_0_48, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 4.44/4.62  cnf(c_0_49, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|esk3_0=esk4_0|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.44/4.62  cnf(c_0_50, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 4.44/4.62  cnf(c_0_51, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 4.44/4.62  cnf(c_0_52, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 4.44/4.62  cnf(c_0_53, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 4.44/4.62  cnf(c_0_54, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 4.44/4.62  cnf(c_0_55, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 4.44/4.62  fof(c_0_56, plain, ![X36, X37, X38, X39, X40, X41, X42, X43, X44, X45]:(((~r2_hidden(X40,X39)|(X40=X36|X40=X37|X40=X38)|X39!=k1_enumset1(X36,X37,X38))&(((X41!=X36|r2_hidden(X41,X39)|X39!=k1_enumset1(X36,X37,X38))&(X41!=X37|r2_hidden(X41,X39)|X39!=k1_enumset1(X36,X37,X38)))&(X41!=X38|r2_hidden(X41,X39)|X39!=k1_enumset1(X36,X37,X38))))&((((esk2_4(X42,X43,X44,X45)!=X42|~r2_hidden(esk2_4(X42,X43,X44,X45),X45)|X45=k1_enumset1(X42,X43,X44))&(esk2_4(X42,X43,X44,X45)!=X43|~r2_hidden(esk2_4(X42,X43,X44,X45),X45)|X45=k1_enumset1(X42,X43,X44)))&(esk2_4(X42,X43,X44,X45)!=X44|~r2_hidden(esk2_4(X42,X43,X44,X45),X45)|X45=k1_enumset1(X42,X43,X44)))&(r2_hidden(esk2_4(X42,X43,X44,X45),X45)|(esk2_4(X42,X43,X44,X45)=X42|esk2_4(X42,X43,X44,X45)=X43|esk2_4(X42,X43,X44,X45)=X44)|X45=k1_enumset1(X42,X43,X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 4.44/4.62  cnf(c_0_57, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_40]), c_0_36])).
% 4.44/4.62  cnf(c_0_58, negated_conjecture, (esk4_0=esk3_0|k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_51]), c_0_28]), c_0_52]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_55])).
% 4.44/4.62  fof(c_0_59, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k4_xboole_0(X9,X10)))&((~r2_hidden(esk1_3(X14,X15,X16),X16)|(~r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X15))|X16=k4_xboole_0(X14,X15))&((r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))&(~r2_hidden(esk1_3(X14,X15,X16),X15)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 4.44/4.62  cnf(c_0_60, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 4.44/4.62  cnf(c_0_61, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_48, c_0_57])).
% 4.44/4.62  cnf(c_0_62, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 4.44/4.62  cnf(c_0_63, negated_conjecture, (k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_58, c_0_29])).
% 4.44/4.62  cnf(c_0_64, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 4.44/4.62  fof(c_0_65, plain, ![X19, X20, X21]:(((~r2_hidden(X19,X20)|~r2_hidden(X19,X21)|~r2_hidden(X19,k5_xboole_0(X20,X21)))&(r2_hidden(X19,X20)|r2_hidden(X19,X21)|~r2_hidden(X19,k5_xboole_0(X20,X21))))&((~r2_hidden(X19,X20)|r2_hidden(X19,X21)|r2_hidden(X19,k5_xboole_0(X20,X21)))&(~r2_hidden(X19,X21)|r2_hidden(X19,X20)|r2_hidden(X19,k5_xboole_0(X20,X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 4.44/4.62  cnf(c_0_66, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_52]), c_0_53]), c_0_54]), c_0_55])).
% 4.44/4.62  cnf(c_0_67, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_36])).
% 4.44/4.62  cnf(c_0_68, negated_conjecture, (k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k3_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))|esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_61, c_0_63])).
% 4.44/4.62  cnf(c_0_69, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_64, c_0_28])).
% 4.44/4.62  cnf(c_0_70, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.44/4.62  fof(c_0_71, plain, ![X24, X25, X26]:k5_xboole_0(k3_xboole_0(X24,X25),k3_xboole_0(X26,X25))=k3_xboole_0(k5_xboole_0(X24,X26),X25), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 4.44/4.62  cnf(c_0_72, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 4.44/4.62  cnf(c_0_73, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X3,X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 4.44/4.62  cnf(c_0_74, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_66])])).
% 4.44/4.62  cnf(c_0_75, negated_conjecture, (k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 4.44/4.62  cnf(c_0_76, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_69])).
% 4.44/4.62  cnf(c_0_77, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|esk3_0!=esk4_0|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.44/4.62  cnf(c_0_78, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 4.44/4.62  cnf(c_0_79, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_50]), c_0_51]), c_0_51]), c_0_28]), c_0_52]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_55])).
% 4.44/4.62  cnf(c_0_80, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 4.44/4.62  cnf(c_0_81, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_61, c_0_67])).
% 4.44/4.62  cnf(c_0_82, plain, (X1=X5|X1=X4|X1=X3|X2!=k5_enumset1(X3,X3,X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_52]), c_0_53]), c_0_54]), c_0_55])).
% 4.44/4.62  cnf(c_0_83, plain, (r2_hidden(X1,k5_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X4,X1)))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 4.44/4.62  cnf(c_0_84, negated_conjecture, (k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))=k3_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))|esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_61, c_0_75])).
% 4.44/4.62  cnf(c_0_85, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_76, c_0_34])).
% 4.44/4.62  cnf(c_0_86, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|esk4_0!=esk3_0|k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))!=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_50]), c_0_51]), c_0_51]), c_0_28]), c_0_52]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_55])).
% 4.44/4.62  fof(c_0_87, plain, ![X74, X75, X76]:((r2_hidden(X76,X75)|k3_xboole_0(k2_tarski(X74,X76),X75)=k1_tarski(X74)|~r2_hidden(X74,X75))&(X74!=X76|k3_xboole_0(k2_tarski(X74,X76),X75)=k1_tarski(X74)|~r2_hidden(X74,X75))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).
% 4.44/4.62  cnf(c_0_88, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X4,X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_52]), c_0_53]), c_0_54]), c_0_55])).
% 4.44/4.62  cnf(c_0_89, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))!=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_79, c_0_29])).
% 4.44/4.62  cnf(c_0_90, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,k5_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_37]), c_0_29]), c_0_81])).
% 4.44/4.62  cnf(c_0_91, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k5_enumset1(X4,X4,X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_82])).
% 4.44/4.62  cnf(c_0_92, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk4_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|r2_hidden(esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 4.44/4.62  cnf(c_0_93, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))!=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk4_0!=esk3_0), inference(rw,[status(thm)],[c_0_86, c_0_29])).
% 4.44/4.62  cnf(c_0_94, plain, (r2_hidden(X1,X2)|k3_xboole_0(k2_tarski(X3,X1),X2)=k1_tarski(X3)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 4.44/4.62  cnf(c_0_95, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X1,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_88])])).
% 4.44/4.62  cnf(c_0_96, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 4.44/4.62  cnf(c_0_97, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))!=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_89, c_0_90])).
% 4.44/4.62  cnf(c_0_98, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 4.44/4.62  cnf(c_0_99, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))!=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk4_0!=esk3_0), inference(rw,[status(thm)],[c_0_93, c_0_90])).
% 4.44/4.62  cnf(c_0_100, plain, (k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X1),X2)=k5_enumset1(X3,X3,X3,X3,X3,X3,X3)|r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_55]), c_0_55])).
% 4.44/4.62  cnf(c_0_101, plain, (r2_hidden(X1,k5_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X1,X4)))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_73, c_0_95])).
% 4.44/4.62  cnf(c_0_102, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_96, c_0_28])).
% 4.44/4.62  cnf(c_0_103, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 4.44/4.62  cnf(c_0_104, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))!=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])).
% 4.44/4.62  cnf(c_0_105, plain, (k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(X3,k5_enumset1(X4,X4,X4,X4,X4,X1,X5)))=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)|r2_hidden(X2,k5_xboole_0(X3,k5_enumset1(X4,X4,X4,X4,X4,X1,X5)))|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 4.44/4.62  cnf(c_0_106, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_102])).
% 4.44/4.62  cnf(c_0_107, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k5_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_90, c_0_29])).
% 4.44/4.62  cnf(c_0_108, negated_conjecture, (esk4_0=esk3_0|~r2_hidden(esk4_0,k5_xboole_0(X1,esk5_0))|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_103, c_0_98])).
% 4.44/4.62  cnf(c_0_109, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))|r2_hidden(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 4.44/4.62  cnf(c_0_110, plain, (~r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,X2)))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_106, c_0_107])).
% 4.44/4.62  cnf(c_0_111, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_39]), c_0_81]), c_0_61]), c_0_74])])).
% 4.44/4.62  cnf(c_0_112, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_107]), c_0_107]), c_0_81]), c_0_107]), c_0_39]), c_0_40]), c_0_36])).
% 4.44/4.62  cnf(c_0_113, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_tarski(esk3_0)|~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.44/4.62  cnf(c_0_114, negated_conjecture, (esk4_0=esk3_0|~r2_hidden(esk3_0,k3_xboole_0(X1,k5_xboole_0(esk5_0,X1)))), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 4.44/4.62  cnf(c_0_115, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X1,X2)))=k3_xboole_0(k5_xboole_0(X1,X3),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_112]), c_0_90])).
% 4.44/4.62  cnf(c_0_116, negated_conjecture, (k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_50]), c_0_51]), c_0_51]), c_0_28]), c_0_52]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_55]), c_0_55]), c_0_55])).
% 4.44/4.62  cnf(c_0_117, plain, (k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)|X1!=X2|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 4.44/4.62  cnf(c_0_118, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 4.44/4.62  cnf(c_0_119, negated_conjecture, (esk4_0=esk3_0|~r2_hidden(esk3_0,k3_xboole_0(k5_xboole_0(X1,esk5_0),k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 4.44/4.62  cnf(c_0_120, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_112, c_0_29])).
% 4.44/4.62  cnf(c_0_121, negated_conjecture, (k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[c_0_116, c_0_29])).
% 4.44/4.62  cnf(c_0_122, plain, (k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),X3)=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)|X1!=X2|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_55]), c_0_55])).
% 4.44/4.62  cnf(c_0_123, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X2,X2,X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_52]), c_0_53]), c_0_54]), c_0_55])).
% 4.44/4.62  cnf(c_0_124, negated_conjecture, (esk4_0=esk3_0|~r2_hidden(esk3_0,k3_xboole_0(k5_xboole_0(X1,esk5_0),k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_119, c_0_120])).
% 4.44/4.62  cnf(c_0_125, negated_conjecture, (k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[c_0_121, c_0_90])).
% 4.44/4.62  cnf(c_0_126, plain, (k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_122])).
% 4.44/4.62  cnf(c_0_127, plain, (r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_123])])).
% 4.44/4.62  cnf(c_0_128, negated_conjecture, (esk4_0=esk3_0|~r2_hidden(esk3_0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,esk5_0)))), inference(spm,[status(thm)],[c_0_124, c_0_29])).
% 4.44/4.62  cnf(c_0_129, negated_conjecture, (k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk4_0=esk3_0), inference(spm,[status(thm)],[c_0_125, c_0_111])).
% 4.44/4.62  cnf(c_0_130, plain, (k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X2,X3))=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 4.44/4.62  cnf(c_0_131, plain, (r2_hidden(X1,k5_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X3,X4)))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_73, c_0_127])).
% 4.44/4.62  cnf(c_0_132, negated_conjecture, (esk4_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_39]), c_0_81]), c_0_61]), c_0_130]), c_0_127])])).
% 4.44/4.62  cnf(c_0_133, plain, (k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(X2,k5_enumset1(X1,X1,X1,X1,X1,X3,X4)))=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_126, c_0_131])).
% 4.44/4.62  cnf(c_0_134, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_132]), c_0_132]), c_0_133])).
% 4.44/4.62  cnf(c_0_135, negated_conjecture, (~r2_hidden(esk3_0,k3_xboole_0(X1,k5_xboole_0(esk5_0,X1)))), inference(spm,[status(thm)],[c_0_110, c_0_134])).
% 4.44/4.62  cnf(c_0_136, negated_conjecture, (~r2_hidden(esk3_0,k3_xboole_0(k5_xboole_0(X1,esk5_0),k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_135, c_0_115])).
% 4.44/4.62  cnf(c_0_137, negated_conjecture, (k3_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_132]), c_0_132]), c_0_134])])).
% 4.44/4.62  cnf(c_0_138, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_81]), c_0_29]), c_0_137]), c_0_127])]), ['proof']).
% 4.44/4.62  # SZS output end CNFRefutation
% 4.44/4.62  # Proof object total steps             : 139
% 4.44/4.62  # Proof object clause steps            : 98
% 4.44/4.62  # Proof object formula steps           : 41
% 4.44/4.62  # Proof object conjectures             : 38
% 4.44/4.62  # Proof object clause conjectures      : 35
% 4.44/4.62  # Proof object formula conjectures     : 3
% 4.44/4.62  # Proof object initial clauses used    : 29
% 4.44/4.62  # Proof object initial formulas used   : 20
% 4.44/4.62  # Proof object generating inferences   : 37
% 4.44/4.62  # Proof object simplifying inferences  : 164
% 4.44/4.62  # Training examples: 0 positive, 0 negative
% 4.44/4.62  # Parsed axioms                        : 22
% 4.44/4.62  # Removed by relevancy pruning/SinE    : 0
% 4.44/4.62  # Initial clauses                      : 41
% 4.44/4.62  # Removed in clause preprocessing      : 7
% 4.44/4.62  # Initial clauses in saturation        : 34
% 4.44/4.62  # Processed clauses                    : 9224
% 4.44/4.62  # ...of these trivial                  : 94
% 4.44/4.62  # ...subsumed                          : 7969
% 4.44/4.62  # ...remaining for further processing  : 1161
% 4.44/4.62  # Other redundant clauses eliminated   : 602
% 4.44/4.62  # Clauses deleted for lack of memory   : 0
% 4.44/4.62  # Backward-subsumed                    : 41
% 4.44/4.62  # Backward-rewritten                   : 404
% 4.44/4.62  # Generated clauses                    : 204450
% 4.44/4.62  # ...of the previous two non-trivial   : 196209
% 4.44/4.62  # Contextual simplify-reflections      : 3
% 4.44/4.62  # Paramodulations                      : 203674
% 4.44/4.62  # Factorizations                       : 174
% 4.44/4.62  # Equation resolutions                 : 605
% 4.44/4.62  # Propositional unsat checks           : 0
% 4.44/4.62  #    Propositional check models        : 0
% 4.44/4.62  #    Propositional check unsatisfiable : 0
% 4.44/4.62  #    Propositional clauses             : 0
% 4.44/4.62  #    Propositional clauses after purity: 0
% 4.44/4.62  #    Propositional unsat core size     : 0
% 4.44/4.62  #    Propositional preprocessing time  : 0.000
% 4.44/4.62  #    Propositional encoding time       : 0.000
% 4.44/4.62  #    Propositional solver time         : 0.000
% 4.44/4.62  #    Success case prop preproc time    : 0.000
% 4.44/4.62  #    Success case prop encoding time   : 0.000
% 4.44/4.62  #    Success case prop solver time     : 0.000
% 4.44/4.62  # Current number of processed clauses  : 674
% 4.44/4.62  #    Positive orientable unit clauses  : 73
% 4.44/4.62  #    Positive unorientable unit clauses: 8
% 4.44/4.62  #    Negative unit clauses             : 71
% 4.44/4.62  #    Non-unit-clauses                  : 522
% 4.44/4.62  # Current number of unprocessed clauses: 186251
% 4.44/4.62  # ...number of literals in the above   : 1167725
% 4.44/4.62  # Current number of archived formulas  : 0
% 4.44/4.62  # Current number of archived clauses   : 486
% 4.44/4.62  # Clause-clause subsumption calls (NU) : 126568
% 4.44/4.62  # Rec. Clause-clause subsumption calls : 66098
% 4.44/4.62  # Non-unit clause-clause subsumptions  : 2936
% 4.44/4.62  # Unit Clause-clause subsumption calls : 5876
% 4.44/4.62  # Rewrite failures with RHS unbound    : 0
% 4.44/4.62  # BW rewrite match attempts            : 509
% 4.44/4.62  # BW rewrite match successes           : 225
% 4.44/4.62  # Condensation attempts                : 0
% 4.44/4.62  # Condensation successes               : 0
% 4.44/4.62  # Termbank termtop insertions          : 6136619
% 4.46/4.64  
% 4.46/4.64  # -------------------------------------------------
% 4.46/4.64  # User time                : 4.183 s
% 4.46/4.64  # System time              : 0.112 s
% 4.46/4.64  # Total time               : 4.295 s
% 4.46/4.64  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
