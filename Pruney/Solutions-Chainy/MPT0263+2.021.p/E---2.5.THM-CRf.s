%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:58 EST 2020

% Result     : Theorem 0.06s
% Output     : CNFRefutation 0.06s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 697 expanded)
%              Number of clauses        :   51 ( 308 expanded)
%              Number of leaves         :   12 ( 191 expanded)
%              Depth                    :   16
%              Number of atoms          :  147 (1176 expanded)
%              Number of equality atoms :   57 ( 690 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t58_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_xboole_0(k1_tarski(X1),X2)
      | k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

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

fof(c_0_12,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k3_xboole_0(X27,X28)) = k4_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_13,plain,(
    ! [X29,X30] : k4_xboole_0(X29,k4_xboole_0(X29,X30)) = k3_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | k3_xboole_0(X16,X17) = k1_xboole_0 )
      & ( k3_xboole_0(X16,X17) != k1_xboole_0
        | r1_xboole_0(X16,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_19,plain,(
    ! [X26] : k4_xboole_0(X26,k1_xboole_0) = X26 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_16]),c_0_16])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_25,plain,(
    ! [X20,X21,X23,X24,X25] :
      ( ( r2_hidden(esk2_2(X20,X21),X20)
        | r1_xboole_0(X20,X21) )
      & ( r2_hidden(esk2_2(X20,X21),X21)
        | r1_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X25,X23)
        | ~ r2_hidden(X25,X24)
        | ~ r1_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_16])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_20,c_0_23])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

fof(c_0_29,plain,(
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

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27])])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_xboole_0(k1_tarski(X1),X2)
        | k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    inference(assume_negation,[status(cth)],[t58_zfmisc_1])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_28])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_37,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk3_0),esk4_0)
    & k3_xboole_0(k1_tarski(esk3_0),esk4_0) != k1_tarski(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

fof(c_0_38,plain,(
    ! [X31] : k2_tarski(X31,X31) = k1_tarski(X31) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_39,plain,(
    ! [X32,X33] : k1_enumset1(X32,X32,X33) = k2_tarski(X32,X33) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_40,plain,(
    ! [X34,X35,X36] : k2_enumset1(X34,X34,X35,X36) = k1_enumset1(X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_16])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])]),c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk3_0),esk4_0) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_16])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_47])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_21])).

cnf(c_0_54,plain,
    ( X1 = k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | r2_hidden(esk1_3(X3,k4_xboole_0(X3,X2),X1),X3)
    | r2_hidden(esk1_3(X3,k4_xboole_0(X3,X2),X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_35])).

fof(c_0_55,plain,(
    ! [X37,X38] :
      ( r2_hidden(X37,X38)
      | r1_xboole_0(k1_tarski(X37),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_2(X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_23])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_61,plain,
    ( r2_hidden(esk2_2(X1,X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_21]),c_0_58])]),c_0_53])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_2(k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k2_enumset1(X1,X1,X1,X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk2_2(k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ r2_hidden(esk2_2(k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.06/0.26  % Computer   : n006.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % WCLimit    : 600
% 0.06/0.26  % DateTime   : Tue Dec  1 16:49:07 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.26  # Version: 2.5pre002
% 0.06/0.26  # No SInE strategy applied
% 0.06/0.26  # Trying AutoSched0 for 299 seconds
% 0.06/0.30  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.06/0.30  # and selection function SelectNegativeLiterals.
% 0.06/0.30  #
% 0.06/0.30  # Preprocessing time       : 0.012 s
% 0.06/0.30  # Presaturation interreduction done
% 0.06/0.30  
% 0.06/0.30  # Proof found!
% 0.06/0.30  # SZS status Theorem
% 0.06/0.30  # SZS output start CNFRefutation
% 0.06/0.30  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.06/0.30  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.06/0.30  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.06/0.30  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.06/0.30  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.06/0.30  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.06/0.30  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.06/0.30  fof(t58_zfmisc_1, conjecture, ![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 0.06/0.30  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.06/0.30  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.06/0.30  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.06/0.30  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.06/0.30  fof(c_0_12, plain, ![X27, X28]:k4_xboole_0(X27,k3_xboole_0(X27,X28))=k4_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.06/0.30  fof(c_0_13, plain, ![X29, X30]:k4_xboole_0(X29,k4_xboole_0(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.06/0.30  fof(c_0_14, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.06/0.30  cnf(c_0_15, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.06/0.30  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.06/0.30  cnf(c_0_17, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.06/0.30  fof(c_0_18, plain, ![X16, X17]:((~r1_xboole_0(X16,X17)|k3_xboole_0(X16,X17)=k1_xboole_0)&(k3_xboole_0(X16,X17)!=k1_xboole_0|r1_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.06/0.30  fof(c_0_19, plain, ![X26]:k4_xboole_0(X26,k1_xboole_0)=X26, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.06/0.30  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.06/0.30  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_16]), c_0_16])).
% 0.06/0.30  cnf(c_0_22, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.06/0.30  cnf(c_0_23, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.06/0.30  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.06/0.30  fof(c_0_25, plain, ![X20, X21, X23, X24, X25]:(((r2_hidden(esk2_2(X20,X21),X20)|r1_xboole_0(X20,X21))&(r2_hidden(esk2_2(X20,X21),X21)|r1_xboole_0(X20,X21)))&(~r2_hidden(X25,X23)|~r2_hidden(X25,X24)|~r1_xboole_0(X23,X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.06/0.30  cnf(c_0_26, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_22, c_0_16])).
% 0.06/0.30  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(spm,[status(thm)],[c_0_20, c_0_23])).
% 0.06/0.30  cnf(c_0_28, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_23])).
% 0.06/0.30  fof(c_0_29, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.06/0.30  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.06/0.30  cnf(c_0_31, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27])])).
% 0.06/0.30  fof(c_0_32, negated_conjecture, ~(![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1))), inference(assume_negation,[status(cth)],[t58_zfmisc_1])).
% 0.06/0.30  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.06/0.30  cnf(c_0_34, plain, (r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))|k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_28])).
% 0.06/0.30  cnf(c_0_35, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.06/0.30  cnf(c_0_36, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.06/0.30  fof(c_0_37, negated_conjecture, (~r1_xboole_0(k1_tarski(esk3_0),esk4_0)&k3_xboole_0(k1_tarski(esk3_0),esk4_0)!=k1_tarski(esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).
% 0.06/0.30  fof(c_0_38, plain, ![X31]:k2_tarski(X31,X31)=k1_tarski(X31), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.06/0.30  fof(c_0_39, plain, ![X32, X33]:k1_enumset1(X32,X32,X33)=k2_tarski(X32,X33), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.06/0.30  fof(c_0_40, plain, ![X34, X35, X36]:k2_enumset1(X34,X34,X35,X36)=k1_enumset1(X34,X35,X36), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.06/0.30  cnf(c_0_41, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_16])).
% 0.06/0.30  cnf(c_0_42, plain, (r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])]), c_0_36])).
% 0.06/0.30  cnf(c_0_43, negated_conjecture, (k3_xboole_0(k1_tarski(esk3_0),esk4_0)!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.06/0.30  cnf(c_0_44, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.06/0.30  cnf(c_0_45, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.06/0.30  cnf(c_0_46, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.06/0.30  cnf(c_0_47, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.06/0.30  cnf(c_0_48, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_21, c_0_23])).
% 0.06/0.30  cnf(c_0_49, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_28])).
% 0.06/0.30  cnf(c_0_50, negated_conjecture, (k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_16])).
% 0.06/0.30  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|r2_hidden(esk2_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_41, c_0_47])).
% 0.06/0.30  cnf(c_0_52, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.06/0.30  cnf(c_0_53, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_50, c_0_21])).
% 0.06/0.30  cnf(c_0_54, plain, (X1=k4_xboole_0(X2,k4_xboole_0(X2,X3))|r2_hidden(esk1_3(X3,k4_xboole_0(X3,X2),X1),X3)|r2_hidden(esk1_3(X3,k4_xboole_0(X3,X2),X1),X1)), inference(spm,[status(thm)],[c_0_21, c_0_35])).
% 0.06/0.30  fof(c_0_55, plain, ![X37, X38]:(r2_hidden(X37,X38)|r1_xboole_0(k1_tarski(X37),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.06/0.30  cnf(c_0_56, plain, (X1=k1_xboole_0|r2_hidden(esk2_2(X1,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_23])).
% 0.06/0.30  cnf(c_0_57, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.06/0.30  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54])])).
% 0.06/0.30  cnf(c_0_59, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.06/0.30  cnf(c_0_60, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.06/0.30  cnf(c_0_61, plain, (r2_hidden(esk2_2(X1,X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_36, c_0_56])).
% 0.06/0.30  cnf(c_0_62, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_21]), c_0_58])]), c_0_53])).
% 0.06/0.30  cnf(c_0_63, plain, (r2_hidden(X1,X2)|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_44]), c_0_45]), c_0_46])).
% 0.06/0.30  cnf(c_0_64, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_60])).
% 0.06/0.30  cnf(c_0_65, negated_conjecture, (r2_hidden(esk2_2(k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.06/0.30  cnf(c_0_66, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k2_enumset1(X1,X1,X1,X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_30, c_0_63])).
% 0.06/0.30  cnf(c_0_67, negated_conjecture, (r2_hidden(esk2_2(k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.06/0.30  cnf(c_0_68, negated_conjecture, (~r1_xboole_0(k1_tarski(esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.06/0.30  cnf(c_0_69, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.06/0.30  cnf(c_0_70, negated_conjecture, (r2_hidden(esk3_0,X1)|~r2_hidden(esk2_2(k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)),X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.06/0.30  cnf(c_0_71, negated_conjecture, (~r1_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_44]), c_0_45]), c_0_46])).
% 0.06/0.30  cnf(c_0_72, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_69])).
% 0.06/0.30  cnf(c_0_73, negated_conjecture, (r2_hidden(esk3_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_70, c_0_65])).
% 0.06/0.30  cnf(c_0_74, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_71, c_0_63])).
% 0.06/0.30  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])]), ['proof']).
% 0.06/0.30  # SZS output end CNFRefutation
% 0.06/0.30  # Proof object total steps             : 76
% 0.06/0.30  # Proof object clause steps            : 51
% 0.06/0.30  # Proof object formula steps           : 25
% 0.06/0.30  # Proof object conjectures             : 16
% 0.06/0.30  # Proof object clause conjectures      : 13
% 0.06/0.30  # Proof object formula conjectures     : 3
% 0.06/0.30  # Proof object initial clauses used    : 18
% 0.06/0.30  # Proof object initial formulas used   : 12
% 0.06/0.30  # Proof object generating inferences   : 22
% 0.06/0.30  # Proof object simplifying inferences  : 35
% 0.06/0.30  # Training examples: 0 positive, 0 negative
% 0.06/0.30  # Parsed axioms                        : 13
% 0.06/0.30  # Removed by relevancy pruning/SinE    : 0
% 0.06/0.30  # Initial clauses                      : 22
% 0.06/0.30  # Removed in clause preprocessing      : 4
% 0.06/0.30  # Initial clauses in saturation        : 18
% 0.06/0.30  # Processed clauses                    : 588
% 0.06/0.30  # ...of these trivial                  : 27
% 0.06/0.30  # ...subsumed                          : 380
% 0.06/0.30  # ...remaining for further processing  : 181
% 0.06/0.30  # Other redundant clauses eliminated   : 148
% 0.06/0.30  # Clauses deleted for lack of memory   : 0
% 0.06/0.30  # Backward-subsumed                    : 3
% 0.06/0.30  # Backward-rewritten                   : 21
% 0.06/0.30  # Generated clauses                    : 5247
% 0.06/0.30  # ...of the previous two non-trivial   : 4204
% 0.06/0.30  # Contextual simplify-reflections      : 2
% 0.06/0.30  # Paramodulations                      : 5097
% 0.06/0.30  # Factorizations                       : 2
% 0.06/0.30  # Equation resolutions                 : 148
% 0.06/0.30  # Propositional unsat checks           : 0
% 0.06/0.30  #    Propositional check models        : 0
% 0.06/0.30  #    Propositional check unsatisfiable : 0
% 0.06/0.30  #    Propositional clauses             : 0
% 0.06/0.30  #    Propositional clauses after purity: 0
% 0.06/0.30  #    Propositional unsat core size     : 0
% 0.06/0.30  #    Propositional preprocessing time  : 0.000
% 0.06/0.30  #    Propositional encoding time       : 0.000
% 0.06/0.30  #    Propositional solver time         : 0.000
% 0.06/0.30  #    Success case prop preproc time    : 0.000
% 0.06/0.30  #    Success case prop encoding time   : 0.000
% 0.06/0.30  #    Success case prop solver time     : 0.000
% 0.06/0.30  # Current number of processed clauses  : 136
% 0.06/0.30  #    Positive orientable unit clauses  : 23
% 0.06/0.30  #    Positive unorientable unit clauses: 1
% 0.06/0.30  #    Negative unit clauses             : 8
% 0.06/0.30  #    Non-unit-clauses                  : 104
% 0.06/0.30  # Current number of unprocessed clauses: 3610
% 0.06/0.30  # ...number of literals in the above   : 11076
% 0.06/0.30  # Current number of archived formulas  : 0
% 0.06/0.30  # Current number of archived clauses   : 46
% 0.06/0.30  # Clause-clause subsumption calls (NU) : 1179
% 0.06/0.30  # Rec. Clause-clause subsumption calls : 1056
% 0.06/0.30  # Non-unit clause-clause subsumptions  : 160
% 0.06/0.30  # Unit Clause-clause subsumption calls : 80
% 0.06/0.30  # Rewrite failures with RHS unbound    : 0
% 0.06/0.30  # BW rewrite match attempts            : 85
% 0.06/0.30  # BW rewrite match successes           : 33
% 0.06/0.30  # Condensation attempts                : 0
% 0.06/0.30  # Condensation successes               : 0
% 0.06/0.30  # Termbank termtop insertions          : 68506
% 0.06/0.30  
% 0.06/0.30  # -------------------------------------------------
% 0.06/0.30  # User time                : 0.038 s
% 0.06/0.30  # System time              : 0.004 s
% 0.06/0.30  # Total time               : 0.042 s
% 0.06/0.30  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
