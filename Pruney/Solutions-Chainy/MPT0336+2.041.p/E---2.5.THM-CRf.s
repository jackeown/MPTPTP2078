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
% DateTime   : Thu Dec  3 10:44:53 EST 2020

% Result     : Theorem 0.97s
% Output     : CNFRefutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 191 expanded)
%              Number of clauses        :   45 (  83 expanded)
%              Number of leaves         :   14 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  158 ( 399 expanded)
%              Number of equality atoms :   41 ( 120 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t74_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,k3_xboole_0(X2,X3))
        & r1_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_15,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))
    & r2_hidden(esk6_0,esk5_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_16,plain,(
    ! [X37] : k2_tarski(X37,X37) = k1_tarski(X37) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X38,X39] : k1_enumset1(X38,X38,X39) = k2_tarski(X38,X39) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X40,X41,X42] : k2_enumset1(X40,X40,X41,X42) = k1_enumset1(X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X43,X44] :
      ( r2_hidden(X43,X44)
      | r1_xboole_0(k1_tarski(X43),X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_25,plain,(
    ! [X20,X21,X23,X24,X25] :
      ( ( r1_xboole_0(X20,X21)
        | r2_hidden(esk2_2(X20,X21),k3_xboole_0(X20,X21)) )
      & ( ~ r2_hidden(X25,k3_xboole_0(X23,X24))
        | ~ r1_xboole_0(X23,X24) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X26,X27,X28] : k3_xboole_0(k3_xboole_0(X26,X27),X28) = k3_xboole_0(X26,k3_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_28,plain,(
    ! [X29,X30] :
      ( ~ r1_tarski(X29,X30)
      | k3_xboole_0(X29,X30) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_33,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_36,plain,(
    ! [X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | k3_xboole_0(X16,X17) = k1_xboole_0 )
      & ( k3_xboole_0(X16,X17) != k1_xboole_0
        | r1_xboole_0(X16,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_37,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) = k3_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_43,plain,(
    ! [X34,X35,X36] :
      ( r1_xboole_0(X34,k3_xboole_0(X35,X36))
      | ~ r1_xboole_0(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_xboole_1])])])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X4,k3_xboole_0(X2,k3_xboole_0(X3,k2_enumset1(X1,X1,X1,X1)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_xboole_0(esk3_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))) = k3_xboole_0(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_33])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_44])).

fof(c_0_51,plain,(
    ! [X18,X19] :
      ( ~ r1_xboole_0(X18,X19)
      | r1_xboole_0(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk6_0,k3_xboole_0(esk4_0,esk3_0))
    | ~ r2_hidden(X1,k3_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0
    | r2_hidden(esk2_2(esk4_0,k3_xboole_0(esk3_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(esk5_0,k3_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_xboole_0(esk4_0,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_44])).

fof(c_0_59,plain,(
    ! [X31,X32,X33] :
      ( ( r1_xboole_0(X31,k2_xboole_0(X32,X33))
        | ~ r1_xboole_0(X31,X32)
        | ~ r1_xboole_0(X31,X33) )
      & ( r1_xboole_0(X31,X32)
        | ~ r1_xboole_0(X31,k2_xboole_0(X32,X33)) )
      & ( r1_xboole_0(X31,X33)
        | ~ r1_xboole_0(X31,k2_xboole_0(X32,X33)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk6_0,k3_xboole_0(X1,esk5_0))
    | ~ r2_hidden(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0
    | r2_hidden(esk6_0,k3_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_56]),c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_50])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_44])).

cnf(c_0_67,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_68,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_33]),c_0_30]),c_0_39]),c_0_30]),c_0_57]),c_0_63]),c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(esk4_0,k2_xboole_0(X1,esk5_0))
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_71]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:22:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.97/1.16  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.97/1.16  # and selection function SelectCQArNTNpEqFirst.
% 0.97/1.16  #
% 0.97/1.16  # Preprocessing time       : 0.028 s
% 0.97/1.16  # Presaturation interreduction done
% 0.97/1.16  
% 0.97/1.16  # Proof found!
% 0.97/1.16  # SZS status Theorem
% 0.97/1.16  # SZS output start CNFRefutation
% 0.97/1.16  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.97/1.16  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.97/1.16  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.97/1.16  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.97/1.16  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.97/1.16  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.97/1.16  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.97/1.16  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.97/1.16  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.97/1.16  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.97/1.16  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.97/1.16  fof(t74_xboole_1, axiom, ![X1, X2, X3]:~((~(r1_xboole_0(X1,k3_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 0.97/1.16  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.97/1.16  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.97/1.16  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.97/1.16  fof(c_0_15, negated_conjecture, (((r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))&r2_hidden(esk6_0,esk5_0))&r1_xboole_0(esk5_0,esk4_0))&~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.97/1.16  fof(c_0_16, plain, ![X37]:k2_tarski(X37,X37)=k1_tarski(X37), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.97/1.16  fof(c_0_17, plain, ![X38, X39]:k1_enumset1(X38,X38,X39)=k2_tarski(X38,X39), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.97/1.16  fof(c_0_18, plain, ![X40, X41, X42]:k2_enumset1(X40,X40,X41,X42)=k1_enumset1(X40,X41,X42), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.97/1.16  fof(c_0_19, plain, ![X43, X44]:(r2_hidden(X43,X44)|r1_xboole_0(k1_tarski(X43),X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.97/1.16  cnf(c_0_20, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.97/1.16  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.97/1.16  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.97/1.16  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.97/1.16  fof(c_0_24, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.97/1.16  fof(c_0_25, plain, ![X20, X21, X23, X24, X25]:((r1_xboole_0(X20,X21)|r2_hidden(esk2_2(X20,X21),k3_xboole_0(X20,X21)))&(~r2_hidden(X25,k3_xboole_0(X23,X24))|~r1_xboole_0(X23,X24))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.97/1.16  cnf(c_0_26, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.97/1.16  fof(c_0_27, plain, ![X26, X27, X28]:k3_xboole_0(k3_xboole_0(X26,X27),X28)=k3_xboole_0(X26,k3_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.97/1.16  fof(c_0_28, plain, ![X29, X30]:(~r1_tarski(X29,X30)|k3_xboole_0(X29,X30)=X29), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.97/1.16  cnf(c_0_29, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])).
% 0.97/1.16  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.97/1.16  cnf(c_0_31, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.97/1.16  cnf(c_0_32, plain, (r2_hidden(X1,X2)|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_21]), c_0_22]), c_0_23])).
% 0.97/1.16  cnf(c_0_33, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.97/1.16  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.97/1.16  cnf(c_0_35, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.97/1.16  fof(c_0_36, plain, ![X16, X17]:((~r1_xboole_0(X16,X17)|k3_xboole_0(X16,X17)=k1_xboole_0)&(k3_xboole_0(X16,X17)!=k1_xboole_0|r1_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.97/1.16  fof(c_0_37, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.97/1.16  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.97/1.16  cnf(c_0_39, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,k3_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_33, c_0_30])).
% 0.97/1.16  cnf(c_0_40, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))=k3_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.97/1.16  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.97/1.16  cnf(c_0_42, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.97/1.16  fof(c_0_43, plain, ![X34, X35, X36]:(r1_xboole_0(X34,k3_xboole_0(X35,X36))|~r1_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_xboole_1])])])).
% 0.97/1.16  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.97/1.16  cnf(c_0_45, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.97/1.16  cnf(c_0_46, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X4,k3_xboole_0(X2,k3_xboole_0(X3,k2_enumset1(X1,X1,X1,X1))))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.97/1.16  cnf(c_0_47, negated_conjecture, (k3_xboole_0(esk4_0,k3_xboole_0(esk3_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))=k3_xboole_0(esk4_0,esk3_0)), inference(rw,[status(thm)],[c_0_40, c_0_33])).
% 0.97/1.16  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.97/1.16  cnf(c_0_49, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.97/1.16  cnf(c_0_50, negated_conjecture, (k3_xboole_0(esk5_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_44])).
% 0.97/1.16  fof(c_0_51, plain, ![X18, X19]:(~r1_xboole_0(X18,X19)|r1_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.97/1.16  cnf(c_0_52, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_45])).
% 0.97/1.16  cnf(c_0_53, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.97/1.16  cnf(c_0_54, negated_conjecture, (r2_hidden(esk6_0,k3_xboole_0(esk4_0,esk3_0))|~r2_hidden(X1,k3_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.97/1.16  cnf(c_0_55, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0|r2_hidden(esk2_2(esk4_0,k3_xboole_0(esk3_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_48, c_0_47])).
% 0.97/1.16  cnf(c_0_56, negated_conjecture, (r1_xboole_0(esk5_0,k3_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_49, c_0_44])).
% 0.97/1.16  cnf(c_0_57, negated_conjecture, (k3_xboole_0(esk5_0,k3_xboole_0(esk4_0,X1))=k3_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_50])).
% 0.97/1.16  cnf(c_0_58, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_44])).
% 0.97/1.16  fof(c_0_59, plain, ![X31, X32, X33]:((r1_xboole_0(X31,k2_xboole_0(X32,X33))|~r1_xboole_0(X31,X32)|~r1_xboole_0(X31,X33))&((r1_xboole_0(X31,X32)|~r1_xboole_0(X31,k2_xboole_0(X32,X33)))&(r1_xboole_0(X31,X33)|~r1_xboole_0(X31,k2_xboole_0(X32,X33))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.97/1.16  cnf(c_0_60, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.97/1.16  cnf(c_0_61, negated_conjecture, (r2_hidden(esk6_0,k3_xboole_0(X1,esk5_0))|~r2_hidden(esk6_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.97/1.16  cnf(c_0_62, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0|r2_hidden(esk6_0,k3_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.97/1.16  cnf(c_0_63, negated_conjecture, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_56]), c_0_57])).
% 0.97/1.16  cnf(c_0_64, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_58, c_0_50])).
% 0.97/1.16  cnf(c_0_65, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.97/1.16  cnf(c_0_66, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_44])).
% 0.97/1.16  cnf(c_0_67, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.97/1.16  cnf(c_0_68, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_33]), c_0_30]), c_0_39]), c_0_30]), c_0_57]), c_0_63]), c_0_64])).
% 0.97/1.16  cnf(c_0_69, negated_conjecture, (r1_xboole_0(esk4_0,k2_xboole_0(X1,esk5_0))|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.97/1.16  cnf(c_0_70, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.97/1.16  cnf(c_0_71, negated_conjecture, (r1_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.97/1.16  cnf(c_0_72, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.97/1.16  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_71]), c_0_72]), ['proof']).
% 0.97/1.16  # SZS output end CNFRefutation
% 0.97/1.16  # Proof object total steps             : 74
% 0.97/1.16  # Proof object clause steps            : 45
% 0.97/1.16  # Proof object formula steps           : 29
% 0.97/1.16  # Proof object conjectures             : 27
% 0.97/1.16  # Proof object clause conjectures      : 24
% 0.97/1.16  # Proof object formula conjectures     : 3
% 0.97/1.16  # Proof object initial clauses used    : 19
% 0.97/1.16  # Proof object initial formulas used   : 14
% 0.97/1.16  # Proof object generating inferences   : 20
% 0.97/1.16  # Proof object simplifying inferences  : 19
% 0.97/1.16  # Training examples: 0 positive, 0 negative
% 0.97/1.16  # Parsed axioms                        : 14
% 0.97/1.16  # Removed by relevancy pruning/SinE    : 0
% 0.97/1.16  # Initial clauses                      : 26
% 0.97/1.16  # Removed in clause preprocessing      : 3
% 0.97/1.16  # Initial clauses in saturation        : 23
% 0.97/1.16  # Processed clauses                    : 11387
% 0.97/1.16  # ...of these trivial                  : 1035
% 0.97/1.16  # ...subsumed                          : 7851
% 0.97/1.16  # ...remaining for further processing  : 2501
% 0.97/1.16  # Other redundant clauses eliminated   : 3
% 0.97/1.16  # Clauses deleted for lack of memory   : 0
% 0.97/1.16  # Backward-subsumed                    : 1
% 0.97/1.16  # Backward-rewritten                   : 310
% 0.97/1.16  # Generated clauses                    : 119216
% 0.97/1.16  # ...of the previous two non-trivial   : 91689
% 0.97/1.16  # Contextual simplify-reflections      : 0
% 0.97/1.16  # Paramodulations                      : 119169
% 0.97/1.16  # Factorizations                       : 44
% 0.97/1.16  # Equation resolutions                 : 3
% 0.97/1.16  # Propositional unsat checks           : 0
% 0.97/1.16  #    Propositional check models        : 0
% 0.97/1.16  #    Propositional check unsatisfiable : 0
% 0.97/1.16  #    Propositional clauses             : 0
% 0.97/1.16  #    Propositional clauses after purity: 0
% 0.97/1.16  #    Propositional unsat core size     : 0
% 0.97/1.16  #    Propositional preprocessing time  : 0.000
% 0.97/1.16  #    Propositional encoding time       : 0.000
% 0.97/1.16  #    Propositional solver time         : 0.000
% 0.97/1.16  #    Success case prop preproc time    : 0.000
% 0.97/1.16  #    Success case prop encoding time   : 0.000
% 0.97/1.16  #    Success case prop solver time     : 0.000
% 0.97/1.16  # Current number of processed clauses  : 2164
% 0.97/1.16  #    Positive orientable unit clauses  : 1545
% 0.97/1.16  #    Positive unorientable unit clauses: 4
% 0.97/1.16  #    Negative unit clauses             : 207
% 0.97/1.16  #    Non-unit-clauses                  : 408
% 0.97/1.16  # Current number of unprocessed clauses: 79710
% 0.97/1.16  # ...number of literals in the above   : 136122
% 0.97/1.16  # Current number of archived formulas  : 0
% 0.97/1.16  # Current number of archived clauses   : 337
% 0.97/1.16  # Clause-clause subsumption calls (NU) : 12888
% 0.97/1.16  # Rec. Clause-clause subsumption calls : 11483
% 0.97/1.16  # Non-unit clause-clause subsumptions  : 130
% 0.97/1.16  # Unit Clause-clause subsumption calls : 11319
% 0.97/1.16  # Rewrite failures with RHS unbound    : 0
% 0.97/1.16  # BW rewrite match attempts            : 23746
% 0.97/1.16  # BW rewrite match successes           : 406
% 0.97/1.16  # Condensation attempts                : 0
% 0.97/1.16  # Condensation successes               : 0
% 0.97/1.16  # Termbank termtop insertions          : 1745324
% 0.97/1.16  
% 0.97/1.16  # -------------------------------------------------
% 0.97/1.16  # User time                : 0.784 s
% 0.97/1.16  # System time              : 0.035 s
% 0.97/1.16  # Total time               : 0.819 s
% 0.97/1.16  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
