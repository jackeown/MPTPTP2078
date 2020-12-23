%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:59 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 120 expanded)
%              Number of clauses        :   40 (  53 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  140 ( 245 expanded)
%              Number of equality atoms :   28 (  52 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

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

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t77_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t90_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_17,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))
    & r2_hidden(esk6_0,esk5_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X41,X42] :
      ( ( k4_xboole_0(X41,k1_tarski(X42)) != X41
        | ~ r2_hidden(X42,X41) )
      & ( r2_hidden(X42,X41)
        | k4_xboole_0(X41,k1_tarski(X42)) = X41 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_19,plain,(
    ! [X35] : k2_tarski(X35,X35) = k1_tarski(X35) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X36,X37] : k1_enumset1(X36,X36,X37) = k2_tarski(X36,X37) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X21,X22] : k4_xboole_0(X21,X22) = k5_xboole_0(X21,k3_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_22,plain,(
    ! [X38,X39,X40] : k2_enumset1(X38,X38,X39,X40) = k1_enumset1(X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r1_xboole_0(X15,X16)
        | r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X20,k3_xboole_0(X18,X19))
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_24,plain,(
    ! [X29,X30] : r1_xboole_0(k4_xboole_0(X29,X30),X30) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_36,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk6_0,X1)
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))) = X1
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_46,plain,(
    ! [X26,X27,X28] :
      ( r1_xboole_0(X26,X27)
      | ~ r1_tarski(X26,X28)
      | ~ r1_xboole_0(X26,k3_xboole_0(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_xboole_1])])])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(X1,k3_xboole_0(esk4_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_28]),c_0_29]),c_0_31])).

fof(c_0_53,plain,(
    ! [X31,X32] :
      ( ( ~ r1_xboole_0(X31,X32)
        | k4_xboole_0(X31,X32) = X31 )
      & ( k4_xboole_0(X31,X32) != X31
        | r1_xboole_0(X31,X32) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(X1,esk4_0)
    | ~ r1_tarski(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_43])).

fof(c_0_56,plain,(
    ! [X33,X34] : r1_xboole_0(k4_xboole_0(X33,k3_xboole_0(X33,X34)),X34) ),
    inference(variable_rename,[status(thm)],[t90_xboole_1])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk4_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_59,plain,(
    ! [X23,X24,X25] :
      ( ( r1_xboole_0(X23,k2_xboole_0(X24,X25))
        | ~ r1_xboole_0(X23,X24)
        | ~ r1_xboole_0(X23,X25) )
      & ( r1_xboole_0(X23,X24)
        | ~ r1_xboole_0(X23,k2_xboole_0(X24,X25)) )
      & ( r1_xboole_0(X23,X25)
        | ~ r1_xboole_0(X23,k2_xboole_0(X24,X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_60,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_57,c_0_30])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_58])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))),X2) ),
    inference(rw,[status(thm)],[c_0_60,c_0_30])).

cnf(c_0_65,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(esk4_0,k2_xboole_0(X1,esk5_0))
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_45])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_68]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:18:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.40/0.61  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.40/0.61  # and selection function SelectLComplex.
% 0.40/0.61  #
% 0.40/0.61  # Preprocessing time       : 0.028 s
% 0.40/0.61  # Presaturation interreduction done
% 0.40/0.61  
% 0.40/0.61  # Proof found!
% 0.40/0.61  # SZS status Theorem
% 0.40/0.61  # SZS output start CNFRefutation
% 0.40/0.61  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.40/0.61  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.40/0.61  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.40/0.61  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.40/0.61  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.40/0.61  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.40/0.61  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.40/0.61  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.40/0.61  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.40/0.61  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.40/0.61  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.40/0.61  fof(t77_xboole_1, axiom, ![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_tarski(X1,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 0.40/0.61  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.40/0.61  fof(t90_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_xboole_1)).
% 0.40/0.61  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.40/0.61  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.40/0.61  fof(c_0_16, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk1_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk1_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.40/0.61  fof(c_0_17, negated_conjecture, (((r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))&r2_hidden(esk6_0,esk5_0))&r1_xboole_0(esk5_0,esk4_0))&~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.40/0.61  fof(c_0_18, plain, ![X41, X42]:((k4_xboole_0(X41,k1_tarski(X42))!=X41|~r2_hidden(X42,X41))&(r2_hidden(X42,X41)|k4_xboole_0(X41,k1_tarski(X42))=X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.40/0.61  fof(c_0_19, plain, ![X35]:k2_tarski(X35,X35)=k1_tarski(X35), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.40/0.61  fof(c_0_20, plain, ![X36, X37]:k1_enumset1(X36,X36,X37)=k2_tarski(X36,X37), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.40/0.61  fof(c_0_21, plain, ![X21, X22]:k4_xboole_0(X21,X22)=k5_xboole_0(X21,k3_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.40/0.61  fof(c_0_22, plain, ![X38, X39, X40]:k2_enumset1(X38,X38,X39,X40)=k1_enumset1(X38,X39,X40), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.40/0.61  fof(c_0_23, plain, ![X15, X16, X18, X19, X20]:((r1_xboole_0(X15,X16)|r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)))&(~r2_hidden(X20,k3_xboole_0(X18,X19))|~r1_xboole_0(X18,X19))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.40/0.61  fof(c_0_24, plain, ![X29, X30]:r1_xboole_0(k4_xboole_0(X29,X30),X30), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.40/0.61  cnf(c_0_25, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.61  cnf(c_0_26, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.61  cnf(c_0_27, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.40/0.61  cnf(c_0_28, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.40/0.61  cnf(c_0_29, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.40/0.61  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.40/0.61  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.40/0.61  fof(c_0_32, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.40/0.61  cnf(c_0_33, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.40/0.61  cnf(c_0_34, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.40/0.61  cnf(c_0_35, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.40/0.61  fof(c_0_36, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.40/0.61  cnf(c_0_37, negated_conjecture, (~r2_hidden(esk6_0,X1)|~r1_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.40/0.61  cnf(c_0_38, plain, (k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.40/0.61  cnf(c_0_39, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.40/0.61  cnf(c_0_40, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.61  cnf(c_0_41, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.40/0.61  cnf(c_0_42, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_35, c_0_30])).
% 0.40/0.61  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.40/0.61  cnf(c_0_44, negated_conjecture, (k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))=X1|~r1_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.40/0.61  cnf(c_0_45, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.40/0.61  fof(c_0_46, plain, ![X26, X27, X28]:(r1_xboole_0(X26,X27)|~r1_tarski(X26,X28)|~r1_xboole_0(X26,k3_xboole_0(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_xboole_1])])])).
% 0.40/0.61  cnf(c_0_47, plain, (r1_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.40/0.61  cnf(c_0_48, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))=esk4_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.40/0.61  cnf(c_0_49, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.61  cnf(c_0_50, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.40/0.61  cnf(c_0_51, negated_conjecture, (r1_xboole_0(X1,k3_xboole_0(esk4_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_43])).
% 0.40/0.61  cnf(c_0_52, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_28]), c_0_29]), c_0_31])).
% 0.40/0.61  fof(c_0_53, plain, ![X31, X32]:((~r1_xboole_0(X31,X32)|k4_xboole_0(X31,X32)=X31)&(k4_xboole_0(X31,X32)!=X31|r1_xboole_0(X31,X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.40/0.61  cnf(c_0_54, negated_conjecture, (r1_xboole_0(X1,esk4_0)|~r1_tarski(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.40/0.61  cnf(c_0_55, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[c_0_52, c_0_43])).
% 0.40/0.61  fof(c_0_56, plain, ![X33, X34]:r1_xboole_0(k4_xboole_0(X33,k3_xboole_0(X33,X34)),X34), inference(variable_rename,[status(thm)],[t90_xboole_1])).
% 0.40/0.61  cnf(c_0_57, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.40/0.61  cnf(c_0_58, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk4_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.40/0.61  fof(c_0_59, plain, ![X23, X24, X25]:((r1_xboole_0(X23,k2_xboole_0(X24,X25))|~r1_xboole_0(X23,X24)|~r1_xboole_0(X23,X25))&((r1_xboole_0(X23,X24)|~r1_xboole_0(X23,k2_xboole_0(X24,X25)))&(r1_xboole_0(X23,X25)|~r1_xboole_0(X23,k2_xboole_0(X24,X25))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.40/0.61  cnf(c_0_60, plain, (r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.40/0.61  cnf(c_0_61, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_57, c_0_30])).
% 0.40/0.61  cnf(c_0_62, negated_conjecture, (r1_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_39, c_0_58])).
% 0.40/0.61  cnf(c_0_63, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.40/0.61  cnf(c_0_64, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))),X2)), inference(rw,[status(thm)],[c_0_60, c_0_30])).
% 0.40/0.61  cnf(c_0_65, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0)))=esk4_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.40/0.61  cnf(c_0_66, negated_conjecture, (r1_xboole_0(esk4_0,k2_xboole_0(X1,esk5_0))|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_63, c_0_45])).
% 0.40/0.61  cnf(c_0_67, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.40/0.61  cnf(c_0_68, negated_conjecture, (r1_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.40/0.61  cnf(c_0_69, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.40/0.61  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_68]), c_0_69]), ['proof']).
% 0.40/0.61  # SZS output end CNFRefutation
% 0.40/0.61  # Proof object total steps             : 71
% 0.40/0.61  # Proof object clause steps            : 40
% 0.40/0.61  # Proof object formula steps           : 31
% 0.40/0.61  # Proof object conjectures             : 22
% 0.40/0.61  # Proof object clause conjectures      : 19
% 0.40/0.61  # Proof object formula conjectures     : 3
% 0.40/0.61  # Proof object initial clauses used    : 19
% 0.40/0.61  # Proof object initial formulas used   : 15
% 0.40/0.61  # Proof object generating inferences   : 15
% 0.40/0.61  # Proof object simplifying inferences  : 14
% 0.40/0.61  # Training examples: 0 positive, 0 negative
% 0.40/0.61  # Parsed axioms                        : 15
% 0.40/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.40/0.61  # Initial clauses                      : 25
% 0.40/0.61  # Removed in clause preprocessing      : 4
% 0.40/0.61  # Initial clauses in saturation        : 21
% 0.40/0.61  # Processed clauses                    : 1173
% 0.40/0.61  # ...of these trivial                  : 266
% 0.40/0.61  # ...subsumed                          : 118
% 0.40/0.61  # ...remaining for further processing  : 789
% 0.40/0.61  # Other redundant clauses eliminated   : 0
% 0.40/0.61  # Clauses deleted for lack of memory   : 0
% 0.40/0.61  # Backward-subsumed                    : 0
% 0.40/0.61  # Backward-rewritten                   : 2
% 0.40/0.61  # Generated clauses                    : 30616
% 0.40/0.61  # ...of the previous two non-trivial   : 27800
% 0.40/0.61  # Contextual simplify-reflections      : 0
% 0.40/0.61  # Paramodulations                      : 30616
% 0.40/0.61  # Factorizations                       : 0
% 0.40/0.61  # Equation resolutions                 : 0
% 0.40/0.61  # Propositional unsat checks           : 0
% 0.40/0.61  #    Propositional check models        : 0
% 0.40/0.61  #    Propositional check unsatisfiable : 0
% 0.40/0.61  #    Propositional clauses             : 0
% 0.40/0.61  #    Propositional clauses after purity: 0
% 0.40/0.61  #    Propositional unsat core size     : 0
% 0.40/0.61  #    Propositional preprocessing time  : 0.000
% 0.40/0.61  #    Propositional encoding time       : 0.000
% 0.40/0.61  #    Propositional solver time         : 0.000
% 0.40/0.61  #    Success case prop preproc time    : 0.000
% 0.40/0.61  #    Success case prop encoding time   : 0.000
% 0.40/0.61  #    Success case prop solver time     : 0.000
% 0.40/0.61  # Current number of processed clauses  : 766
% 0.40/0.61  #    Positive orientable unit clauses  : 574
% 0.40/0.61  #    Positive unorientable unit clauses: 1
% 0.40/0.61  #    Negative unit clauses             : 8
% 0.40/0.61  #    Non-unit-clauses                  : 183
% 0.40/0.61  # Current number of unprocessed clauses: 26637
% 0.40/0.61  # ...number of literals in the above   : 28162
% 0.40/0.61  # Current number of archived formulas  : 0
% 0.40/0.61  # Current number of archived clauses   : 27
% 0.40/0.61  # Clause-clause subsumption calls (NU) : 4057
% 0.40/0.61  # Rec. Clause-clause subsumption calls : 3966
% 0.40/0.61  # Non-unit clause-clause subsumptions  : 104
% 0.40/0.61  # Unit Clause-clause subsumption calls : 1128
% 0.40/0.61  # Rewrite failures with RHS unbound    : 0
% 0.40/0.61  # BW rewrite match attempts            : 2803
% 0.40/0.61  # BW rewrite match successes           : 11
% 0.40/0.61  # Condensation attempts                : 0
% 0.40/0.61  # Condensation successes               : 0
% 0.40/0.61  # Termbank termtop insertions          : 611535
% 0.40/0.61  
% 0.40/0.61  # -------------------------------------------------
% 0.40/0.61  # User time                : 0.240 s
% 0.40/0.61  # System time              : 0.021 s
% 0.40/0.61  # Total time               : 0.262 s
% 0.40/0.61  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
