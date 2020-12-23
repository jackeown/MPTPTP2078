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
% DateTime   : Thu Dec  3 10:44:58 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 445 expanded)
%              Number of clauses        :   64 ( 206 expanded)
%              Number of leaves         :   16 ( 115 expanded)
%              Depth                    :   17
%              Number of atoms          :  165 ( 975 expanded)
%              Number of equality atoms :   47 ( 261 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

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

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

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
    ! [X25,X26] : r1_xboole_0(k4_xboole_0(X25,X26),X26) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_18,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k5_xboole_0(X15,k3_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k3_xboole_0(X7,X8) = k1_xboole_0 )
      & ( k3_xboole_0(X7,X8) != k1_xboole_0
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_20,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))
    & r2_hidden(esk5_0,esk4_0)
    & r1_xboole_0(esk4_0,esk3_0)
    & ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_21,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_27,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_28,plain,(
    ! [X27,X28] :
      ( ( ~ r1_xboole_0(X27,X28)
        | k4_xboole_0(X27,X28) = X27 )
      & ( k4_xboole_0(X27,X28) != X27
        | r1_xboole_0(X27,X28) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_29,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_30,plain,(
    ! [X32] : k2_tarski(X32,X32) = k1_tarski(X32) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_31,plain,(
    ! [X33,X34] : k1_enumset1(X33,X33,X34) = k2_tarski(X33,X34) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_32,plain,(
    ! [X35,X36,X37] : k2_enumset1(X35,X35,X36,X37) = k1_enumset1(X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_33,plain,(
    ! [X38,X39] :
      ( ( k4_xboole_0(X38,k1_tarski(X39)) != X38
        | ~ r2_hidden(X39,X38) )
      & ( r2_hidden(X39,X38)
        | k4_xboole_0(X38,k1_tarski(X39)) = X38 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk4_0,k1_xboole_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_39,plain,(
    ! [X17,X18] : r1_tarski(k4_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_40,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_41,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(X29,X30)
      | r1_xboole_0(X29,k4_xboole_0(X31,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_34]),c_0_35])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_22])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_53,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_55,plain,(
    ! [X21] : r1_xboole_0(X21,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(esk5_0,X1)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_46])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_43]),c_0_44]),c_0_22]),c_0_45])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(esk3_0,k5_xboole_0(esk4_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_xboole_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_24]),c_0_26])).

cnf(c_0_62,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_53,c_0_22])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_22]),c_0_22])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_56,c_0_22])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_35])).

cnf(c_0_68,negated_conjecture,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) = X1
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_25])).

cnf(c_0_71,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk3_0,esk2_0),k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_70])).

cnf(c_0_76,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_71])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_65]),c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk3_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_75])).

cnf(c_0_80,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_52])).

cnf(c_0_81,plain,
    ( r1_xboole_0(k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_75]),c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_78]),c_0_35])).

cnf(c_0_83,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[c_0_79,c_0_77])).

fof(c_0_84,plain,(
    ! [X22,X23,X24] :
      ( ( r1_xboole_0(X22,k2_xboole_0(X23,X24))
        | ~ r1_xboole_0(X22,X23)
        | ~ r1_xboole_0(X22,X24) )
      & ( r1_xboole_0(X22,X23)
        | ~ r1_xboole_0(X22,k2_xboole_0(X23,X24)) )
      & ( r1_xboole_0(X22,X24)
        | ~ r1_xboole_0(X22,k2_xboole_0(X23,X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_85,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_52])).

cnf(c_0_86,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_79]),c_0_83])).

cnf(c_0_87,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( r1_xboole_0(X1,k3_xboole_0(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(X1,esk4_0))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_69])).

cnf(c_0_90,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_35])).

cnf(c_0_91,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(esk3_0,esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(esk3_0,X1)),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_77])).

cnf(c_0_95,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_94]),c_0_95]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:23:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.77/0.96  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.77/0.96  # and selection function SelectLComplex.
% 0.77/0.96  #
% 0.77/0.96  # Preprocessing time       : 0.038 s
% 0.77/0.96  # Presaturation interreduction done
% 0.77/0.96  
% 0.77/0.96  # Proof found!
% 0.77/0.96  # SZS status Theorem
% 0.77/0.96  # SZS output start CNFRefutation
% 0.77/0.96  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.77/0.96  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.77/0.96  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.77/0.96  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.77/0.96  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.77/0.96  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.77/0.96  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.77/0.96  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.77/0.96  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.77/0.96  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.77/0.96  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.77/0.96  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.77/0.96  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.77/0.96  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.77/0.96  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.77/0.96  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.77/0.96  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.77/0.96  fof(c_0_17, plain, ![X25, X26]:r1_xboole_0(k4_xboole_0(X25,X26),X26), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.77/0.96  fof(c_0_18, plain, ![X15, X16]:k4_xboole_0(X15,X16)=k5_xboole_0(X15,k3_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.77/0.96  fof(c_0_19, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k3_xboole_0(X7,X8)=k1_xboole_0)&(k3_xboole_0(X7,X8)!=k1_xboole_0|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.77/0.96  fof(c_0_20, negated_conjecture, (((r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))&r2_hidden(esk5_0,esk4_0))&r1_xboole_0(esk4_0,esk3_0))&~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.77/0.96  cnf(c_0_21, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.77/0.96  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.77/0.96  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.77/0.96  cnf(c_0_24, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.77/0.96  cnf(c_0_25, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.77/0.96  cnf(c_0_26, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.77/0.96  fof(c_0_27, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.77/0.96  fof(c_0_28, plain, ![X27, X28]:((~r1_xboole_0(X27,X28)|k4_xboole_0(X27,X28)=X27)&(k4_xboole_0(X27,X28)!=X27|r1_xboole_0(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.77/0.96  fof(c_0_29, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk1_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk1_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.77/0.96  fof(c_0_30, plain, ![X32]:k2_tarski(X32,X32)=k1_tarski(X32), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.77/0.96  fof(c_0_31, plain, ![X33, X34]:k1_enumset1(X33,X33,X34)=k2_tarski(X33,X34), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.77/0.96  fof(c_0_32, plain, ![X35, X36, X37]:k2_enumset1(X35,X35,X36,X37)=k1_enumset1(X35,X36,X37), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.77/0.96  fof(c_0_33, plain, ![X38, X39]:((k4_xboole_0(X38,k1_tarski(X39))!=X38|~r2_hidden(X39,X38))&(r2_hidden(X39,X38)|k4_xboole_0(X38,k1_tarski(X39))=X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.77/0.96  cnf(c_0_34, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk4_0,k1_xboole_0),esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.77/0.96  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.77/0.96  cnf(c_0_36, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.77/0.96  cnf(c_0_37, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.77/0.96  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.77/0.96  fof(c_0_39, plain, ![X17, X18]:r1_tarski(k4_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.77/0.96  fof(c_0_40, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.77/0.96  fof(c_0_41, plain, ![X29, X30, X31]:(~r1_tarski(X29,X30)|r1_xboole_0(X29,k4_xboole_0(X31,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.77/0.96  cnf(c_0_42, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.77/0.96  cnf(c_0_43, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.77/0.96  cnf(c_0_44, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.77/0.96  cnf(c_0_45, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.77/0.96  cnf(c_0_46, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.77/0.96  cnf(c_0_47, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.77/0.96  cnf(c_0_48, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.77/0.96  cnf(c_0_49, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_34]), c_0_35])).
% 0.77/0.96  cnf(c_0_50, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_22])).
% 0.77/0.96  cnf(c_0_51, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.77/0.96  cnf(c_0_52, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.77/0.96  cnf(c_0_53, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.77/0.96  cnf(c_0_54, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.77/0.96  fof(c_0_55, plain, ![X21]:r1_xboole_0(X21,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.77/0.96  cnf(c_0_56, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.77/0.96  cnf(c_0_57, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,esk3_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45])).
% 0.77/0.96  cnf(c_0_58, negated_conjecture, (~r2_hidden(esk5_0,X1)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_46])).
% 0.77/0.96  cnf(c_0_59, plain, (k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_43]), c_0_44]), c_0_22]), c_0_45])).
% 0.77/0.96  cnf(c_0_60, negated_conjecture, (r1_xboole_0(esk3_0,k5_xboole_0(esk4_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.77/0.96  cnf(c_0_61, negated_conjecture, (k5_xboole_0(esk4_0,k1_xboole_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_24]), c_0_26])).
% 0.77/0.96  cnf(c_0_62, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.77/0.96  cnf(c_0_63, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_53, c_0_22])).
% 0.77/0.96  cnf(c_0_64, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_22]), c_0_22])).
% 0.77/0.96  cnf(c_0_65, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.77/0.96  cnf(c_0_66, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_56, c_0_22])).
% 0.77/0.96  cnf(c_0_67, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk2_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[c_0_57, c_0_35])).
% 0.77/0.96  cnf(c_0_68, negated_conjecture, (k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))=X1|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.77/0.96  cnf(c_0_69, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.77/0.96  cnf(c_0_70, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_62, c_0_25])).
% 0.77/0.96  cnf(c_0_71, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.77/0.96  cnf(c_0_72, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_65])).
% 0.77/0.96  cnf(c_0_73, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk3_0,esk2_0),k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.77/0.96  cnf(c_0_74, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))=esk3_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.77/0.96  cnf(c_0_75, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_70])).
% 0.77/0.96  cnf(c_0_76, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_66, c_0_71])).
% 0.77/0.96  cnf(c_0_77, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_65]), c_0_72])).
% 0.77/0.96  cnf(c_0_78, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk3_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.77/0.96  cnf(c_0_79, plain, (k5_xboole_0(X1,k1_xboole_0)=k3_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_64, c_0_75])).
% 0.77/0.96  cnf(c_0_80, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_37, c_0_52])).
% 0.77/0.96  cnf(c_0_81, plain, (r1_xboole_0(k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_75]), c_0_77])).
% 0.77/0.96  cnf(c_0_82, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_78]), c_0_35])).
% 0.77/0.96  cnf(c_0_83, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[c_0_79, c_0_77])).
% 0.77/0.96  fof(c_0_84, plain, ![X22, X23, X24]:((r1_xboole_0(X22,k2_xboole_0(X23,X24))|~r1_xboole_0(X22,X23)|~r1_xboole_0(X22,X24))&((r1_xboole_0(X22,X23)|~r1_xboole_0(X22,k2_xboole_0(X23,X24)))&(r1_xboole_0(X22,X24)|~r1_xboole_0(X22,k2_xboole_0(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.77/0.96  cnf(c_0_85, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_80, c_0_52])).
% 0.77/0.96  cnf(c_0_86, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_79]), c_0_83])).
% 0.77/0.96  cnf(c_0_87, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.77/0.96  cnf(c_0_88, negated_conjecture, (r1_xboole_0(X1,k3_xboole_0(esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.77/0.96  cnf(c_0_89, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(X1,esk4_0))|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_87, c_0_69])).
% 0.77/0.96  cnf(c_0_90, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_70, c_0_35])).
% 0.77/0.96  cnf(c_0_91, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(esk3_0,esk2_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_88])).
% 0.77/0.96  cnf(c_0_92, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(esk3_0,X1)),esk4_0))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.77/0.96  cnf(c_0_93, negated_conjecture, (k3_xboole_0(esk3_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_91])).
% 0.77/0.96  cnf(c_0_94, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_77])).
% 0.77/0.96  cnf(c_0_95, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.77/0.96  cnf(c_0_96, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_94]), c_0_95]), ['proof']).
% 0.77/0.96  # SZS output end CNFRefutation
% 0.77/0.96  # Proof object total steps             : 97
% 0.77/0.96  # Proof object clause steps            : 64
% 0.77/0.96  # Proof object formula steps           : 33
% 0.77/0.96  # Proof object conjectures             : 29
% 0.77/0.96  # Proof object clause conjectures      : 26
% 0.77/0.96  # Proof object formula conjectures     : 3
% 0.77/0.96  # Proof object initial clauses used    : 22
% 0.77/0.96  # Proof object initial formulas used   : 16
% 0.77/0.96  # Proof object generating inferences   : 32
% 0.77/0.96  # Proof object simplifying inferences  : 25
% 0.77/0.96  # Training examples: 0 positive, 0 negative
% 0.77/0.96  # Parsed axioms                        : 16
% 0.77/0.96  # Removed by relevancy pruning/SinE    : 0
% 0.77/0.96  # Initial clauses                      : 26
% 0.77/0.96  # Removed in clause preprocessing      : 4
% 0.77/0.96  # Initial clauses in saturation        : 22
% 0.77/0.96  # Processed clauses                    : 3107
% 0.77/0.96  # ...of these trivial                  : 673
% 0.77/0.96  # ...subsumed                          : 688
% 0.77/0.96  # ...remaining for further processing  : 1746
% 0.77/0.96  # Other redundant clauses eliminated   : 22
% 0.77/0.96  # Clauses deleted for lack of memory   : 0
% 0.77/0.96  # Backward-subsumed                    : 0
% 0.77/0.96  # Backward-rewritten                   : 61
% 0.77/0.96  # Generated clauses                    : 86496
% 0.77/0.96  # ...of the previous two non-trivial   : 65831
% 0.77/0.96  # Contextual simplify-reflections      : 0
% 0.77/0.96  # Paramodulations                      : 86474
% 0.77/0.96  # Factorizations                       : 0
% 0.77/0.96  # Equation resolutions                 : 22
% 0.77/0.96  # Propositional unsat checks           : 0
% 0.77/0.96  #    Propositional check models        : 0
% 0.77/0.96  #    Propositional check unsatisfiable : 0
% 0.77/0.96  #    Propositional clauses             : 0
% 0.77/0.96  #    Propositional clauses after purity: 0
% 0.77/0.96  #    Propositional unsat core size     : 0
% 0.77/0.96  #    Propositional preprocessing time  : 0.000
% 0.77/0.96  #    Propositional encoding time       : 0.000
% 0.77/0.96  #    Propositional solver time         : 0.000
% 0.77/0.96  #    Success case prop preproc time    : 0.000
% 0.77/0.96  #    Success case prop encoding time   : 0.000
% 0.77/0.96  #    Success case prop solver time     : 0.000
% 0.77/0.96  # Current number of processed clauses  : 1663
% 0.77/0.96  #    Positive orientable unit clauses  : 1443
% 0.77/0.96  #    Positive unorientable unit clauses: 1
% 0.77/0.96  #    Negative unit clauses             : 41
% 0.77/0.96  #    Non-unit-clauses                  : 178
% 0.77/0.96  # Current number of unprocessed clauses: 62588
% 0.77/0.96  # ...number of literals in the above   : 66555
% 0.77/0.96  # Current number of archived formulas  : 0
% 0.77/0.96  # Current number of archived clauses   : 87
% 0.77/0.96  # Clause-clause subsumption calls (NU) : 6506
% 0.77/0.96  # Rec. Clause-clause subsumption calls : 6452
% 0.77/0.96  # Non-unit clause-clause subsumptions  : 451
% 0.77/0.96  # Unit Clause-clause subsumption calls : 2995
% 0.77/0.96  # Rewrite failures with RHS unbound    : 0
% 0.77/0.96  # BW rewrite match attempts            : 31416
% 0.77/0.96  # BW rewrite match successes           : 39
% 0.77/0.96  # Condensation attempts                : 0
% 0.77/0.96  # Condensation successes               : 0
% 0.77/0.96  # Termbank termtop insertions          : 1723415
% 0.77/0.96  
% 0.77/0.96  # -------------------------------------------------
% 0.77/0.96  # User time                : 0.580 s
% 0.77/0.96  # System time              : 0.039 s
% 0.77/0.96  # Total time               : 0.619 s
% 0.77/0.96  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
