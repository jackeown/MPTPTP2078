%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:49 EST 2020

% Result     : Theorem 1.00s
% Output     : CNFRefutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 219 expanded)
%              Number of clauses        :   54 (  97 expanded)
%              Number of leaves         :   15 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  170 ( 494 expanded)
%              Number of equality atoms :   55 ( 158 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(t57_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X3,X2)
        & ~ r1_xboole_0(k2_tarski(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t78_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X46,X47,X48] :
      ( r2_hidden(X46,X47)
      | r2_hidden(X48,X47)
      | r1_xboole_0(k2_tarski(X46,X48),X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_zfmisc_1])])])).

fof(c_0_17,plain,(
    ! [X41,X42] : k1_enumset1(X41,X41,X42) = k2_tarski(X41,X42) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X43,X44,X45] : k2_enumset1(X43,X43,X44,X45) = k1_enumset1(X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))
    & r2_hidden(esk6_0,esk5_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_20,plain,(
    ! [X40] : k2_tarski(X40,X40) = k1_tarski(X40) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X22,X23,X25,X26,X27] :
      ( ( r1_xboole_0(X22,X23)
        | r2_hidden(esk2_2(X22,X23),k3_xboole_0(X22,X23)) )
      & ( ~ r2_hidden(X27,k3_xboole_0(X25,X26))
        | ~ r1_xboole_0(X25,X26) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | r1_xboole_0(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_28,plain,(
    ! [X18,X19] :
      ( ( ~ r1_xboole_0(X18,X19)
        | k3_xboole_0(X18,X19) = k1_xboole_0 )
      & ( k3_xboole_0(X18,X19) != k1_xboole_0
        | r1_xboole_0(X18,X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | r2_hidden(X1,X2)
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

fof(c_0_31,plain,(
    ! [X30,X31] :
      ( ~ r1_tarski(X30,X31)
      | k3_xboole_0(X30,X31) = X30 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_23]),c_0_24])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X4,k3_xboole_0(k2_enumset1(X1,X1,X1,X3),X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

fof(c_0_41,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | ~ r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X14)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X15)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X15)
        | r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X4,k3_xboole_0(X2,k2_enumset1(X3,X3,X3,X1))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) = k3_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk6_0,k3_xboole_0(esk4_0,esk3_0))
    | ~ r2_hidden(X1,k3_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(esk4_0,esk3_0)) = k1_xboole_0
    | r2_hidden(esk6_0,k3_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk6_0,k3_xboole_0(X1,esk5_0))
    | ~ r2_hidden(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(esk4_0,esk3_0)) = k1_xboole_0
    | r2_hidden(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_57,plain,(
    ! [X35,X36,X37] :
      ( ~ r1_xboole_0(X35,X36)
      | k3_xboole_0(X35,k2_xboole_0(X36,X37)) = k3_xboole_0(X35,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).

fof(c_0_58,plain,(
    ! [X38,X39] : k2_xboole_0(X38,X39) = k5_xboole_0(X38,k4_xboole_0(X39,X38)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_59,plain,(
    ! [X28,X29] : k4_xboole_0(X28,X29) = k5_xboole_0(X28,k3_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(esk4_0,esk3_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_33]),c_0_40]),c_0_44])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk4_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_40])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(k3_xboole_0(esk4_0,esk3_0),X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_65])).

cnf(c_0_69,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_70,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_71,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0)))) = k3_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_43])).

cnf(c_0_73,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_75,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_76,plain,(
    ! [X20,X21] :
      ( ~ r1_xboole_0(X20,X21)
      | r1_xboole_0(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0))))
    | k3_xboole_0(esk4_0,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_63]),c_0_64])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_63]),c_0_63]),c_0_64]),c_0_64])).

cnf(c_0_81,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_33])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_33])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:11:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.00/1.19  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 1.00/1.19  # and selection function SelectCQArNTNpEqFirst.
% 1.00/1.19  #
% 1.00/1.19  # Preprocessing time       : 0.027 s
% 1.00/1.19  # Presaturation interreduction done
% 1.00/1.19  
% 1.00/1.19  # Proof found!
% 1.00/1.19  # SZS status Theorem
% 1.00/1.19  # SZS output start CNFRefutation
% 1.00/1.19  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 1.00/1.19  fof(t57_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X2))&~(r2_hidden(X3,X2)))&~(r1_xboole_0(k2_tarski(X1,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 1.00/1.19  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.00/1.19  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.00/1.19  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.00/1.19  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.00/1.19  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.00/1.19  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.00/1.19  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.00/1.19  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.00/1.19  fof(t78_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 1.00/1.19  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.00/1.19  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.00/1.19  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.00/1.19  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.00/1.19  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 1.00/1.19  fof(c_0_16, plain, ![X46, X47, X48]:(r2_hidden(X46,X47)|r2_hidden(X48,X47)|r1_xboole_0(k2_tarski(X46,X48),X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_zfmisc_1])])])).
% 1.00/1.19  fof(c_0_17, plain, ![X41, X42]:k1_enumset1(X41,X41,X42)=k2_tarski(X41,X42), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.00/1.19  fof(c_0_18, plain, ![X43, X44, X45]:k2_enumset1(X43,X43,X44,X45)=k1_enumset1(X43,X44,X45), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.00/1.19  fof(c_0_19, negated_conjecture, (((r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))&r2_hidden(esk6_0,esk5_0))&r1_xboole_0(esk5_0,esk4_0))&~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 1.00/1.19  fof(c_0_20, plain, ![X40]:k2_tarski(X40,X40)=k1_tarski(X40), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.00/1.19  fof(c_0_21, plain, ![X22, X23, X25, X26, X27]:((r1_xboole_0(X22,X23)|r2_hidden(esk2_2(X22,X23),k3_xboole_0(X22,X23)))&(~r2_hidden(X27,k3_xboole_0(X25,X26))|~r1_xboole_0(X25,X26))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 1.00/1.19  cnf(c_0_22, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|r1_xboole_0(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.00/1.19  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.00/1.19  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.00/1.19  cnf(c_0_25, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.00/1.19  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.00/1.19  fof(c_0_27, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.00/1.19  fof(c_0_28, plain, ![X18, X19]:((~r1_xboole_0(X18,X19)|k3_xboole_0(X18,X19)=k1_xboole_0)&(k3_xboole_0(X18,X19)!=k1_xboole_0|r1_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 1.00/1.19  cnf(c_0_29, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.00/1.19  cnf(c_0_30, plain, (r2_hidden(X3,X2)|r2_hidden(X1,X2)|r1_xboole_0(k2_enumset1(X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 1.00/1.19  fof(c_0_31, plain, ![X30, X31]:(~r1_tarski(X30,X31)|k3_xboole_0(X30,X31)=X30), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 1.00/1.19  cnf(c_0_32, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_23]), c_0_24])).
% 1.00/1.19  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.00/1.19  cnf(c_0_34, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.00/1.19  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.00/1.19  cnf(c_0_36, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|~r2_hidden(X4,k3_xboole_0(k2_enumset1(X1,X1,X1,X3),X2))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.00/1.19  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.00/1.19  cnf(c_0_38, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 1.00/1.19  cnf(c_0_39, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_34])).
% 1.00/1.19  cnf(c_0_40, negated_conjecture, (k3_xboole_0(esk5_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 1.00/1.19  fof(c_0_41, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10))&(r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|~r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k3_xboole_0(X9,X10)))&((~r2_hidden(esk1_3(X14,X15,X16),X16)|(~r2_hidden(esk1_3(X14,X15,X16),X14)|~r2_hidden(esk1_3(X14,X15,X16),X15))|X16=k3_xboole_0(X14,X15))&((r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))&(r2_hidden(esk1_3(X14,X15,X16),X15)|r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 1.00/1.19  cnf(c_0_42, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|~r2_hidden(X4,k3_xboole_0(X2,k2_enumset1(X3,X3,X3,X1)))), inference(spm,[status(thm)],[c_0_36, c_0_33])).
% 1.00/1.19  cnf(c_0_43, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))=k3_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.00/1.19  cnf(c_0_44, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 1.00/1.19  cnf(c_0_45, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.00/1.19  cnf(c_0_46, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.00/1.19  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.00/1.19  cnf(c_0_48, negated_conjecture, (r2_hidden(esk6_0,k3_xboole_0(esk4_0,esk3_0))|~r2_hidden(X1,k3_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.00/1.19  cnf(c_0_49, negated_conjecture, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 1.00/1.19  cnf(c_0_50, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_46])).
% 1.00/1.19  cnf(c_0_51, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.00/1.19  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_47])).
% 1.00/1.19  cnf(c_0_53, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(esk4_0,esk3_0))=k1_xboole_0|r2_hidden(esk6_0,k3_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.00/1.19  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.00/1.19  cnf(c_0_55, negated_conjecture, (r2_hidden(esk6_0,k3_xboole_0(X1,esk5_0))|~r2_hidden(esk6_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.00/1.19  cnf(c_0_56, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(esk4_0,esk3_0))=k1_xboole_0|r2_hidden(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.00/1.19  fof(c_0_57, plain, ![X35, X36, X37]:(~r1_xboole_0(X35,X36)|k3_xboole_0(X35,k2_xboole_0(X36,X37))=k3_xboole_0(X35,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).
% 1.00/1.19  fof(c_0_58, plain, ![X38, X39]:k2_xboole_0(X38,X39)=k5_xboole_0(X38,k4_xboole_0(X39,X38)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 1.00/1.19  fof(c_0_59, plain, ![X28, X29]:k4_xboole_0(X28,X29)=k5_xboole_0(X28,k3_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.00/1.19  cnf(c_0_60, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X2,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_33])).
% 1.00/1.19  cnf(c_0_61, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(esk4_0,esk3_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_33]), c_0_40]), c_0_44])).
% 1.00/1.19  cnf(c_0_62, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.00/1.19  cnf(c_0_63, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.00/1.19  cnf(c_0_64, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 1.00/1.19  cnf(c_0_65, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk4_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 1.00/1.19  cnf(c_0_66, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 1.00/1.19  cnf(c_0_67, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_40])).
% 1.00/1.19  cnf(c_0_68, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(k3_xboole_0(esk4_0,esk3_0),X2))), inference(spm,[status(thm)],[c_0_29, c_0_65])).
% 1.00/1.19  cnf(c_0_69, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.00/1.19  fof(c_0_70, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.00/1.19  cnf(c_0_71, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0))))=k3_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 1.00/1.19  cnf(c_0_72, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_68, c_0_43])).
% 1.00/1.19  cnf(c_0_73, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_35, c_0_69])).
% 1.00/1.19  cnf(c_0_74, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.00/1.19  cnf(c_0_75, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 1.00/1.19  fof(c_0_76, plain, ![X20, X21]:(~r1_xboole_0(X20,X21)|r1_xboole_0(X21,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 1.00/1.19  cnf(c_0_77, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0))))|k3_xboole_0(esk4_0,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_71])).
% 1.00/1.19  cnf(c_0_78, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 1.00/1.19  cnf(c_0_79, negated_conjecture, (~r1_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_63]), c_0_64])).
% 1.00/1.19  cnf(c_0_80, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_63]), c_0_63]), c_0_64]), c_0_64])).
% 1.00/1.19  cnf(c_0_81, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 1.00/1.19  cnf(c_0_82, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_33])).
% 1.00/1.19  cnf(c_0_83, negated_conjecture, (~r1_xboole_0(k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80]), c_0_33])).
% 1.00/1.19  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83]), ['proof']).
% 1.00/1.19  # SZS output end CNFRefutation
% 1.00/1.19  # Proof object total steps             : 85
% 1.00/1.19  # Proof object clause steps            : 54
% 1.00/1.19  # Proof object formula steps           : 31
% 1.00/1.19  # Proof object conjectures             : 30
% 1.00/1.19  # Proof object clause conjectures      : 27
% 1.00/1.19  # Proof object formula conjectures     : 3
% 1.00/1.19  # Proof object initial clauses used    : 22
% 1.00/1.19  # Proof object initial formulas used   : 15
% 1.00/1.19  # Proof object generating inferences   : 22
% 1.00/1.19  # Proof object simplifying inferences  : 24
% 1.00/1.19  # Training examples: 0 positive, 0 negative
% 1.00/1.19  # Parsed axioms                        : 16
% 1.00/1.19  # Removed by relevancy pruning/SinE    : 0
% 1.00/1.19  # Initial clauses                      : 26
% 1.00/1.19  # Removed in clause preprocessing      : 5
% 1.00/1.19  # Initial clauses in saturation        : 21
% 1.00/1.19  # Processed clauses                    : 4649
% 1.00/1.19  # ...of these trivial                  : 672
% 1.00/1.19  # ...subsumed                          : 2694
% 1.00/1.19  # ...remaining for further processing  : 1283
% 1.00/1.19  # Other redundant clauses eliminated   : 3
% 1.00/1.19  # Clauses deleted for lack of memory   : 0
% 1.00/1.19  # Backward-subsumed                    : 4
% 1.00/1.19  # Backward-rewritten                   : 100
% 1.00/1.19  # Generated clauses                    : 66702
% 1.00/1.19  # ...of the previous two non-trivial   : 51311
% 1.00/1.19  # Contextual simplify-reflections      : 0
% 1.00/1.19  # Paramodulations                      : 66669
% 1.00/1.19  # Factorizations                       : 30
% 1.00/1.19  # Equation resolutions                 : 3
% 1.00/1.19  # Propositional unsat checks           : 0
% 1.00/1.19  #    Propositional check models        : 0
% 1.00/1.19  #    Propositional check unsatisfiable : 0
% 1.00/1.19  #    Propositional clauses             : 0
% 1.00/1.19  #    Propositional clauses after purity: 0
% 1.00/1.19  #    Propositional unsat core size     : 0
% 1.00/1.19  #    Propositional preprocessing time  : 0.000
% 1.00/1.19  #    Propositional encoding time       : 0.000
% 1.00/1.19  #    Propositional solver time         : 0.000
% 1.00/1.19  #    Success case prop preproc time    : 0.000
% 1.00/1.19  #    Success case prop encoding time   : 0.000
% 1.00/1.19  #    Success case prop solver time     : 0.000
% 1.00/1.19  # Current number of processed clauses  : 1155
% 1.00/1.19  #    Positive orientable unit clauses  : 945
% 1.00/1.19  #    Positive unorientable unit clauses: 4
% 1.00/1.19  #    Negative unit clauses             : 15
% 1.00/1.19  #    Non-unit-clauses                  : 191
% 1.00/1.19  # Current number of unprocessed clauses: 46394
% 1.00/1.19  # ...number of literals in the above   : 62624
% 1.00/1.19  # Current number of archived formulas  : 0
% 1.00/1.19  # Current number of archived clauses   : 130
% 1.00/1.19  # Clause-clause subsumption calls (NU) : 7346
% 1.00/1.19  # Rec. Clause-clause subsumption calls : 5577
% 1.00/1.19  # Non-unit clause-clause subsumptions  : 437
% 1.00/1.19  # Unit Clause-clause subsumption calls : 3693
% 1.00/1.19  # Rewrite failures with RHS unbound    : 0
% 1.00/1.19  # BW rewrite match attempts            : 100358
% 1.00/1.19  # BW rewrite match successes           : 96
% 1.00/1.19  # Condensation attempts                : 0
% 1.00/1.19  # Condensation successes               : 0
% 1.00/1.19  # Termbank termtop insertions          : 1822700
% 1.00/1.20  
% 1.00/1.20  # -------------------------------------------------
% 1.00/1.20  # User time                : 0.816 s
% 1.00/1.20  # System time              : 0.036 s
% 1.00/1.20  # Total time               : 0.852 s
% 1.00/1.20  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
