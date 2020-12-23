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
% DateTime   : Thu Dec  3 10:44:57 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   96 (1810 expanded)
%              Number of clauses        :   63 ( 811 expanded)
%              Number of leaves         :   16 ( 474 expanded)
%              Depth                    :   22
%              Number of atoms          :  164 (3683 expanded)
%              Number of equality atoms :   57 (1232 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

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

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k3_xboole_0(X7,X8) = k1_xboole_0 )
      & ( k3_xboole_0(X7,X8) != k1_xboole_0
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_18,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_19,plain,(
    ! [X31,X32] :
      ( ( ~ r1_xboole_0(X31,X32)
        | k4_xboole_0(X31,X32) = X31 )
      & ( k4_xboole_0(X31,X32) != X31
        | r1_xboole_0(X31,X32) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_20,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))
    & r2_hidden(esk5_0,esk4_0)
    & r1_xboole_0(esk4_0,esk3_0)
    & ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_21,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_22,plain,(
    ! [X39,X40] :
      ( ( k4_xboole_0(X39,k1_tarski(X40)) != X39
        | ~ r2_hidden(X40,X39) )
      & ( r2_hidden(X40,X39)
        | k4_xboole_0(X39,k1_tarski(X40)) = X39 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_23,plain,(
    ! [X33] : k2_tarski(X33,X33) = k1_tarski(X33) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_24,plain,(
    ! [X34,X35] : k1_enumset1(X34,X34,X35) = k2_tarski(X34,X35) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X36,X37,X38] : k2_enumset1(X36,X36,X37,X38) = k1_enumset1(X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_36,plain,(
    ! [X29,X30] : r1_xboole_0(k4_xboole_0(X29,X30),X30) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(esk5_0,X1)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_41,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_29]),c_0_38])).

fof(c_0_43,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k3_xboole_0(X20,X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_44,plain,(
    ! [X22,X23] : r1_tarski(k4_xboole_0(X22,X23),X22) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = X1
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_47,c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_50])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_51,c_0_27])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_57,plain,(
    ! [X9,X10] :
      ( ~ r1_xboole_0(X9,X10)
      | r1_xboole_0(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_60,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

fof(c_0_63,plain,(
    ! [X17,X18,X19] : k3_xboole_0(k3_xboole_0(X17,X18),X19) = k3_xboole_0(X17,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_27]),c_0_27])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_28,c_0_62])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_27]),c_0_27]),c_0_27]),c_0_27])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_38]),c_0_71]),c_0_71]),c_0_68]),c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_33]),c_0_34]),c_0_35]),c_0_27])).

fof(c_0_76,plain,(
    ! [X26,X27,X28] :
      ( ( r1_xboole_0(X26,k2_xboole_0(X27,X28))
        | ~ r1_xboole_0(X26,X27)
        | ~ r1_xboole_0(X26,X28) )
      & ( r1_xboole_0(X26,X27)
        | ~ r1_xboole_0(X26,k2_xboole_0(X27,X28)) )
      & ( r1_xboole_0(X26,X28)
        | ~ r1_xboole_0(X26,k2_xboole_0(X27,X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_74])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_48]),c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_75,c_0_67])).

cnf(c_0_80,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_70])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_79]),c_0_70])).

cnf(c_0_84,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_29])).

cnf(c_0_85,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,X1),k2_xboole_0(X2,esk4_0))
    | ~ r1_xboole_0(k4_xboole_0(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_82]),c_0_70]),c_0_70])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))) = k4_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_83]),c_0_78])).

cnf(c_0_88,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_67]),c_0_70])).

cnf(c_0_89,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,X1),k2_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_41])).

cnf(c_0_91,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_67]),c_0_87]),c_0_88]),c_0_71]),c_0_69]),c_0_67]),c_0_89]),c_0_71]),c_0_69]),c_0_71])).

cnf(c_0_92,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(X1,esk4_0),k4_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_91]),c_0_69])).

cnf(c_0_94,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:30:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.59  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.19/0.59  # and selection function SelectLComplex.
% 0.19/0.59  #
% 0.19/0.59  # Preprocessing time       : 0.039 s
% 0.19/0.59  # Presaturation interreduction done
% 0.19/0.59  
% 0.19/0.59  # Proof found!
% 0.19/0.59  # SZS status Theorem
% 0.19/0.59  # SZS output start CNFRefutation
% 0.19/0.59  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.19/0.59  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.59  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.59  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.19/0.59  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.59  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.19/0.59  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.59  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.59  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.59  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.19/0.59  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.59  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.59  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.59  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.59  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.19/0.59  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.19/0.59  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.19/0.59  fof(c_0_17, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k3_xboole_0(X7,X8)=k1_xboole_0)&(k3_xboole_0(X7,X8)!=k1_xboole_0|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.59  fof(c_0_18, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.59  fof(c_0_19, plain, ![X31, X32]:((~r1_xboole_0(X31,X32)|k4_xboole_0(X31,X32)=X31)&(k4_xboole_0(X31,X32)!=X31|r1_xboole_0(X31,X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.19/0.59  fof(c_0_20, negated_conjecture, (((r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))&r2_hidden(esk5_0,esk4_0))&r1_xboole_0(esk4_0,esk3_0))&~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.19/0.59  fof(c_0_21, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk1_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk1_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.59  fof(c_0_22, plain, ![X39, X40]:((k4_xboole_0(X39,k1_tarski(X40))!=X39|~r2_hidden(X40,X39))&(r2_hidden(X40,X39)|k4_xboole_0(X39,k1_tarski(X40))=X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.19/0.59  fof(c_0_23, plain, ![X33]:k2_tarski(X33,X33)=k1_tarski(X33), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.59  fof(c_0_24, plain, ![X34, X35]:k1_enumset1(X34,X34,X35)=k2_tarski(X34,X35), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.59  fof(c_0_25, plain, ![X36, X37, X38]:k2_enumset1(X36,X36,X37,X38)=k1_enumset1(X36,X37,X38), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.59  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.59  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.59  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.59  cnf(c_0_29, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.59  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.59  cnf(c_0_31, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.59  cnf(c_0_32, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.59  cnf(c_0_33, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.59  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.59  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.59  fof(c_0_36, plain, ![X29, X30]:r1_xboole_0(k4_xboole_0(X29,X30),X30), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.19/0.59  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.59  cnf(c_0_38, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.59  cnf(c_0_39, negated_conjecture, (~r2_hidden(esk5_0,X1)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.59  cnf(c_0_40, plain, (k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.59  cnf(c_0_41, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.59  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk4_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_29]), c_0_38])).
% 0.19/0.59  fof(c_0_43, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k3_xboole_0(X20,X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.59  fof(c_0_44, plain, ![X22, X23]:r1_tarski(k4_xboole_0(X22,X23),X22), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.59  cnf(c_0_45, negated_conjecture, (k4_xboole_0(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=X1|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.59  cnf(c_0_46, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.59  cnf(c_0_47, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.59  cnf(c_0_48, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.59  cnf(c_0_49, negated_conjecture, (k4_xboole_0(k1_xboole_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.59  cnf(c_0_50, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.59  cnf(c_0_51, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.59  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_47, c_0_27])).
% 0.19/0.59  cnf(c_0_53, negated_conjecture, (r1_tarski(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.59  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_30, c_0_50])).
% 0.19/0.59  cnf(c_0_55, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_51, c_0_27])).
% 0.19/0.59  cnf(c_0_56, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.59  fof(c_0_57, plain, ![X9, X10]:(~r1_xboole_0(X9,X10)|r1_xboole_0(X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.59  cnf(c_0_58, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_54, c_0_50])).
% 0.19/0.59  cnf(c_0_59, negated_conjecture, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.59  fof(c_0_60, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.59  cnf(c_0_61, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.59  cnf(c_0_62, negated_conjecture, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.59  fof(c_0_63, plain, ![X17, X18, X19]:k3_xboole_0(k3_xboole_0(X17,X18),X19)=k3_xboole_0(X17,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.19/0.59  cnf(c_0_64, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.59  cnf(c_0_65, negated_conjecture, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.59  cnf(c_0_66, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.59  cnf(c_0_67, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_27]), c_0_27])).
% 0.19/0.59  cnf(c_0_68, negated_conjecture, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_65])).
% 0.19/0.59  cnf(c_0_69, negated_conjecture, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_28, c_0_62])).
% 0.19/0.59  cnf(c_0_70, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_27]), c_0_27]), c_0_27]), c_0_27])).
% 0.19/0.59  cnf(c_0_71, negated_conjecture, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.19/0.59  cnf(c_0_72, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_38]), c_0_71]), c_0_71]), c_0_68]), c_0_69])).
% 0.19/0.59  cnf(c_0_73, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.59  cnf(c_0_74, negated_conjecture, (r1_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_55, c_0_72])).
% 0.19/0.59  cnf(c_0_75, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_33]), c_0_34]), c_0_35]), c_0_27])).
% 0.19/0.59  fof(c_0_76, plain, ![X26, X27, X28]:((r1_xboole_0(X26,k2_xboole_0(X27,X28))|~r1_xboole_0(X26,X27)|~r1_xboole_0(X26,X28))&((r1_xboole_0(X26,X27)|~r1_xboole_0(X26,k2_xboole_0(X27,X28)))&(r1_xboole_0(X26,X28)|~r1_xboole_0(X26,k2_xboole_0(X27,X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.19/0.59  cnf(c_0_77, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)),esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_74])).
% 0.19/0.59  cnf(c_0_78, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_48]), c_0_67])).
% 0.19/0.59  cnf(c_0_79, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[c_0_75, c_0_67])).
% 0.19/0.59  cnf(c_0_80, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.59  cnf(c_0_81, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.59  cnf(c_0_82, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_48, c_0_70])).
% 0.19/0.59  cnf(c_0_83, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))))=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_79]), c_0_70])).
% 0.19/0.59  cnf(c_0_84, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_29])).
% 0.19/0.59  cnf(c_0_85, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,X1),k2_xboole_0(X2,esk4_0))|~r1_xboole_0(k4_xboole_0(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.59  cnf(c_0_86, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))))))))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_82]), c_0_70]), c_0_70])).
% 0.19/0.59  cnf(c_0_87, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))=k4_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_83]), c_0_78])).
% 0.19/0.59  cnf(c_0_88, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))=k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_67]), c_0_70])).
% 0.19/0.59  cnf(c_0_89, negated_conjecture, (k4_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk3_0), inference(spm,[status(thm)],[c_0_45, c_0_84])).
% 0.19/0.59  cnf(c_0_90, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,X1),k2_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_85, c_0_41])).
% 0.19/0.59  cnf(c_0_91, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), c_0_67]), c_0_87]), c_0_88]), c_0_71]), c_0_69]), c_0_67]), c_0_89]), c_0_71]), c_0_69]), c_0_71])).
% 0.19/0.59  cnf(c_0_92, negated_conjecture, (r1_xboole_0(k2_xboole_0(X1,esk4_0),k4_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_61, c_0_90])).
% 0.19/0.59  cnf(c_0_93, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_91]), c_0_69])).
% 0.19/0.59  cnf(c_0_94, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.59  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94]), ['proof']).
% 0.19/0.59  # SZS output end CNFRefutation
% 0.19/0.59  # Proof object total steps             : 96
% 0.19/0.59  # Proof object clause steps            : 63
% 0.19/0.59  # Proof object formula steps           : 33
% 0.19/0.59  # Proof object conjectures             : 37
% 0.19/0.59  # Proof object clause conjectures      : 34
% 0.19/0.59  # Proof object formula conjectures     : 3
% 0.19/0.59  # Proof object initial clauses used    : 21
% 0.19/0.59  # Proof object initial formulas used   : 16
% 0.19/0.59  # Proof object generating inferences   : 34
% 0.19/0.59  # Proof object simplifying inferences  : 42
% 0.19/0.59  # Training examples: 0 positive, 0 negative
% 0.19/0.59  # Parsed axioms                        : 16
% 0.19/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.59  # Initial clauses                      : 26
% 0.19/0.59  # Removed in clause preprocessing      : 4
% 0.19/0.59  # Initial clauses in saturation        : 22
% 0.19/0.59  # Processed clauses                    : 1267
% 0.19/0.59  # ...of these trivial                  : 197
% 0.19/0.59  # ...subsumed                          : 639
% 0.19/0.59  # ...remaining for further processing  : 431
% 0.19/0.59  # Other redundant clauses eliminated   : 36
% 0.19/0.59  # Clauses deleted for lack of memory   : 0
% 0.19/0.59  # Backward-subsumed                    : 2
% 0.19/0.59  # Backward-rewritten                   : 46
% 0.19/0.59  # Generated clauses                    : 16030
% 0.19/0.59  # ...of the previous two non-trivial   : 8889
% 0.19/0.59  # Contextual simplify-reflections      : 0
% 0.19/0.59  # Paramodulations                      : 15994
% 0.19/0.59  # Factorizations                       : 0
% 0.19/0.59  # Equation resolutions                 : 36
% 0.19/0.59  # Propositional unsat checks           : 0
% 0.19/0.59  #    Propositional check models        : 0
% 0.19/0.59  #    Propositional check unsatisfiable : 0
% 0.19/0.59  #    Propositional clauses             : 0
% 0.19/0.59  #    Propositional clauses after purity: 0
% 0.19/0.59  #    Propositional unsat core size     : 0
% 0.19/0.59  #    Propositional preprocessing time  : 0.000
% 0.19/0.59  #    Propositional encoding time       : 0.000
% 0.19/0.59  #    Propositional solver time         : 0.000
% 0.19/0.59  #    Success case prop preproc time    : 0.000
% 0.19/0.59  #    Success case prop encoding time   : 0.000
% 0.19/0.59  #    Success case prop solver time     : 0.000
% 0.19/0.59  # Current number of processed clauses  : 361
% 0.19/0.59  #    Positive orientable unit clauses  : 273
% 0.19/0.59  #    Positive unorientable unit clauses: 4
% 0.19/0.59  #    Negative unit clauses             : 20
% 0.19/0.59  #    Non-unit-clauses                  : 64
% 0.19/0.59  # Current number of unprocessed clauses: 7559
% 0.19/0.59  # ...number of literals in the above   : 9389
% 0.19/0.59  # Current number of archived formulas  : 0
% 0.19/0.59  # Current number of archived clauses   : 74
% 0.19/0.59  # Clause-clause subsumption calls (NU) : 965
% 0.19/0.59  # Rec. Clause-clause subsumption calls : 956
% 0.19/0.59  # Non-unit clause-clause subsumptions  : 239
% 0.19/0.59  # Unit Clause-clause subsumption calls : 143
% 0.19/0.59  # Rewrite failures with RHS unbound    : 0
% 0.19/0.59  # BW rewrite match attempts            : 835
% 0.19/0.59  # BW rewrite match successes           : 66
% 0.19/0.59  # Condensation attempts                : 0
% 0.19/0.59  # Condensation successes               : 0
% 0.19/0.59  # Termbank termtop insertions          : 341175
% 0.19/0.59  
% 0.19/0.59  # -------------------------------------------------
% 0.19/0.59  # User time                : 0.235 s
% 0.19/0.59  # System time              : 0.013 s
% 0.19/0.59  # Total time               : 0.249 s
% 0.19/0.59  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
