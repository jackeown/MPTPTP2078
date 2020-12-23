%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:38 EST 2020

% Result     : Theorem 0.52s
% Output     : CNFRefutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 692 expanded)
%              Number of clauses        :   69 ( 316 expanded)
%              Number of leaves         :   18 ( 166 expanded)
%              Depth                    :   15
%              Number of atoms          :  245 (2393 expanded)
%              Number of equality atoms :   48 ( 334 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

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

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

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

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & ( k10_relat_1(esk6_0,esk5_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk6_0),esk5_0) )
    & ( k10_relat_1(esk6_0,esk5_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk6_0),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_20,plain,(
    ! [X15] :
      ( X15 = k1_xboole_0
      | r2_hidden(esk2_1(X15),X15) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_21,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_22,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_23,plain,(
    ! [X52,X53,X54,X56] :
      ( ( r2_hidden(esk4_3(X52,X53,X54),k2_relat_1(X54))
        | ~ r2_hidden(X52,k10_relat_1(X54,X53))
        | ~ v1_relat_1(X54) )
      & ( r2_hidden(k4_tarski(X52,esk4_3(X52,X53,X54)),X54)
        | ~ r2_hidden(X52,k10_relat_1(X54,X53))
        | ~ v1_relat_1(X54) )
      & ( r2_hidden(esk4_3(X52,X53,X54),X53)
        | ~ r2_hidden(X52,k10_relat_1(X54,X53))
        | ~ v1_relat_1(X54) )
      & ( ~ r2_hidden(X56,k2_relat_1(X54))
        | ~ r2_hidden(k4_tarski(X52,X56),X54)
        | ~ r2_hidden(X56,X53)
        | r2_hidden(X52,k10_relat_1(X54,X53))
        | ~ v1_relat_1(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_24,negated_conjecture,
    ( k10_relat_1(esk6_0,esk5_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))
    | ~ r1_xboole_0(k2_relat_1(esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_3(X1,X2,esk6_0),X2)
    | ~ r2_hidden(X1,k10_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))
    | r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_37,plain,(
    ! [X46,X47,X48,X50] :
      ( ( r2_hidden(esk3_3(X46,X47,X48),k1_relat_1(X48))
        | ~ r2_hidden(X46,k9_relat_1(X48,X47))
        | ~ v1_relat_1(X48) )
      & ( r2_hidden(k4_tarski(esk3_3(X46,X47,X48),X46),X48)
        | ~ r2_hidden(X46,k9_relat_1(X48,X47))
        | ~ v1_relat_1(X48) )
      & ( r2_hidden(esk3_3(X46,X47,X48),X47)
        | ~ r2_hidden(X46,k9_relat_1(X48,X47))
        | ~ v1_relat_1(X48) )
      & ( ~ r2_hidden(X50,k1_relat_1(X48))
        | ~ r2_hidden(k4_tarski(X50,X46),X48)
        | ~ r2_hidden(X50,X47)
        | r2_hidden(X46,k9_relat_1(X48,X47))
        | ~ v1_relat_1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_38,plain,(
    ! [X51] :
      ( ~ v1_relat_1(X51)
      | k9_relat_1(X51,k1_relat_1(X51)) = k2_relat_1(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk4_3(X1,X2,esk6_0),k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,k10_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_33])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),esk5_0)
    | r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_44,plain,(
    ! [X44,X45] : k1_setfam_1(k2_tarski(X44,X45)) = k3_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_45,plain,(
    ! [X21,X22] : k1_enumset1(X21,X21,X22) = k2_tarski(X21,X22) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_46,plain,(
    ! [X57,X58,X59] :
      ( ( r2_hidden(X57,k1_relat_1(X59))
        | ~ r2_hidden(k4_tarski(X57,X58),X59)
        | ~ v1_relat_1(X59) )
      & ( r2_hidden(X58,k2_relat_1(X59))
        | ~ r2_hidden(k4_tarski(X57,X58),X59)
        | ~ v1_relat_1(X59) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),k2_relat_1(esk6_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),esk5_0)
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0)
    | r2_hidden(esk1_2(X1,esk5_0),X1)
    | ~ r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_53,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_54,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,esk6_0),X1),esk6_0)
    | ~ r2_hidden(X1,k9_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_29])).

cnf(c_0_59,negated_conjecture,
    ( k9_relat_1(esk6_0,k1_relat_1(esk6_0)) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_29])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),k2_relat_1(esk6_0))
    | ~ r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),esk5_0)
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_40])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)
    | r2_hidden(esk1_2(esk5_0,X1),X1)
    | ~ r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),k2_relat_1(esk6_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_41])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))
    | r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_49])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)
    | r2_hidden(esk1_2(esk5_0,X1),esk5_0)
    | ~ r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_51])).

fof(c_0_66,plain,(
    ! [X41,X42,X43] :
      ( ( r2_hidden(X41,X42)
        | ~ r2_hidden(X41,k4_xboole_0(X42,k1_tarski(X43))) )
      & ( X41 != X43
        | ~ r2_hidden(X41,k4_xboole_0(X42,k1_tarski(X43))) )
      & ( ~ r2_hidden(X41,X42)
        | X41 = X43
        | r2_hidden(X41,k4_xboole_0(X42,k1_tarski(X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_67,plain,(
    ! [X20] : k2_tarski(X20,X20) = k1_tarski(X20) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_69,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_70,plain,(
    ! [X23,X24,X25] : k2_enumset1(X23,X23,X24,X25) = k1_enumset1(X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_71,plain,(
    ! [X26,X27,X28,X29] : k3_enumset1(X26,X26,X27,X28,X29) = k2_enumset1(X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_72,plain,(
    ! [X30,X31,X32,X33,X34] : k4_enumset1(X30,X30,X31,X32,X33,X34) = k3_enumset1(X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_73,plain,(
    ! [X35,X36,X37,X38,X39,X40] : k5_enumset1(X35,X35,X36,X37,X38,X39,X40) = k4_enumset1(X35,X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(X1,k1_relat_1(esk6_0),esk6_0),X1),esk6_0)
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),k2_relat_1(esk6_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0)
    | r2_hidden(esk1_2(X1,k2_relat_1(esk6_0)),X1)
    | ~ r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_64])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0)
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_63])).

cnf(c_0_80,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_81,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_83,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_84,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_85,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_86,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

fof(c_0_87,plain,(
    ! [X19] : k4_xboole_0(k1_xboole_0,X19) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk6_0,X2))
    | ~ r2_hidden(k4_tarski(X1,X3),esk6_0)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_29])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),esk1_2(k2_relat_1(esk6_0),esk5_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),X1)
    | ~ r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_77])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_92,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k5_enumset1(X3,X3,X3,X3,X3,X3,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81]),c_0_55]),c_0_82]),c_0_83]),c_0_83]),c_0_84]),c_0_84]),c_0_85]),c_0_85]),c_0_86]),c_0_86])).

cnf(c_0_93,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),k10_relat_1(esk6_0,X1))
    | ~ r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_96,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))))) ),
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_97,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_82]),c_0_83]),c_0_84]),c_0_85]),c_0_86])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),k10_relat_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( k10_relat_1(esk6_0,esk5_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_100,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),X1)
    | ~ r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_101])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_76])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_91])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.52/0.72  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.52/0.72  # and selection function SelectNegativeLiterals.
% 0.52/0.72  #
% 0.52/0.72  # Preprocessing time       : 0.028 s
% 0.52/0.72  # Presaturation interreduction done
% 0.52/0.72  
% 0.52/0.72  # Proof found!
% 0.52/0.72  # SZS status Theorem
% 0.52/0.72  # SZS output start CNFRefutation
% 0.52/0.72  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.52/0.72  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.52/0.72  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.52/0.72  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.52/0.72  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.52/0.72  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.52/0.72  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.52/0.72  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.52/0.72  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.52/0.72  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 0.52/0.72  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.52/0.72  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.52/0.72  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.52/0.72  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.52/0.72  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.52/0.72  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.52/0.72  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.52/0.72  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.52/0.72  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.52/0.72  fof(c_0_19, negated_conjecture, (v1_relat_1(esk6_0)&((k10_relat_1(esk6_0,esk5_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk6_0),esk5_0))&(k10_relat_1(esk6_0,esk5_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk6_0),esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.52/0.72  fof(c_0_20, plain, ![X15]:(X15=k1_xboole_0|r2_hidden(esk2_1(X15),X15)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.52/0.72  fof(c_0_21, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.52/0.72  fof(c_0_22, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk1_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk1_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.52/0.72  fof(c_0_23, plain, ![X52, X53, X54, X56]:((((r2_hidden(esk4_3(X52,X53,X54),k2_relat_1(X54))|~r2_hidden(X52,k10_relat_1(X54,X53))|~v1_relat_1(X54))&(r2_hidden(k4_tarski(X52,esk4_3(X52,X53,X54)),X54)|~r2_hidden(X52,k10_relat_1(X54,X53))|~v1_relat_1(X54)))&(r2_hidden(esk4_3(X52,X53,X54),X53)|~r2_hidden(X52,k10_relat_1(X54,X53))|~v1_relat_1(X54)))&(~r2_hidden(X56,k2_relat_1(X54))|~r2_hidden(k4_tarski(X52,X56),X54)|~r2_hidden(X56,X53)|r2_hidden(X52,k10_relat_1(X54,X53))|~v1_relat_1(X54))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.52/0.72  cnf(c_0_24, negated_conjecture, (k10_relat_1(esk6_0,esk5_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.52/0.72  cnf(c_0_25, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.52/0.72  cnf(c_0_26, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.52/0.72  cnf(c_0_27, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.52/0.72  cnf(c_0_28, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.52/0.72  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.52/0.72  cnf(c_0_30, negated_conjecture, (r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))|~r1_xboole_0(k2_relat_1(esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.52/0.72  cnf(c_0_31, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.52/0.72  cnf(c_0_32, plain, (r2_hidden(esk4_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.52/0.72  cnf(c_0_33, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.52/0.72  cnf(c_0_34, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.52/0.72  cnf(c_0_35, negated_conjecture, (r2_hidden(esk4_3(X1,X2,esk6_0),X2)|~r2_hidden(X1,k10_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.52/0.72  cnf(c_0_36, negated_conjecture, (r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))|r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.52/0.72  fof(c_0_37, plain, ![X46, X47, X48, X50]:((((r2_hidden(esk3_3(X46,X47,X48),k1_relat_1(X48))|~r2_hidden(X46,k9_relat_1(X48,X47))|~v1_relat_1(X48))&(r2_hidden(k4_tarski(esk3_3(X46,X47,X48),X46),X48)|~r2_hidden(X46,k9_relat_1(X48,X47))|~v1_relat_1(X48)))&(r2_hidden(esk3_3(X46,X47,X48),X47)|~r2_hidden(X46,k9_relat_1(X48,X47))|~v1_relat_1(X48)))&(~r2_hidden(X50,k1_relat_1(X48))|~r2_hidden(k4_tarski(X50,X46),X48)|~r2_hidden(X50,X47)|r2_hidden(X46,k9_relat_1(X48,X47))|~v1_relat_1(X48))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.52/0.72  fof(c_0_38, plain, ![X51]:(~v1_relat_1(X51)|k9_relat_1(X51,k1_relat_1(X51))=k2_relat_1(X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.52/0.72  cnf(c_0_39, negated_conjecture, (r2_hidden(esk4_3(X1,X2,esk6_0),k2_relat_1(esk6_0))|~r2_hidden(X1,k10_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 0.52/0.72  cnf(c_0_40, negated_conjecture, (r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_30, c_0_27])).
% 0.52/0.72  cnf(c_0_41, negated_conjecture, (r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_33])).
% 0.52/0.72  cnf(c_0_42, plain, (r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_34, c_0_27])).
% 0.52/0.72  cnf(c_0_43, negated_conjecture, (r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),esk5_0)|r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.52/0.72  fof(c_0_44, plain, ![X44, X45]:k1_setfam_1(k2_tarski(X44,X45))=k3_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.52/0.72  fof(c_0_45, plain, ![X21, X22]:k1_enumset1(X21,X21,X22)=k2_tarski(X21,X22), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.52/0.72  fof(c_0_46, plain, ![X57, X58, X59]:((r2_hidden(X57,k1_relat_1(X59))|~r2_hidden(k4_tarski(X57,X58),X59)|~v1_relat_1(X59))&(r2_hidden(X58,k2_relat_1(X59))|~r2_hidden(k4_tarski(X57,X58),X59)|~v1_relat_1(X59))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.52/0.72  cnf(c_0_47, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.52/0.72  cnf(c_0_48, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.52/0.72  cnf(c_0_49, negated_conjecture, (r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),k2_relat_1(esk6_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.52/0.72  cnf(c_0_50, plain, (r2_hidden(esk1_2(X1,X2),X2)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_34, c_0_33])).
% 0.52/0.72  cnf(c_0_51, negated_conjecture, (r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),esk5_0)|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_41])).
% 0.52/0.72  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0)|r2_hidden(esk1_2(X1,esk5_0),X1)|~r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.52/0.72  fof(c_0_53, plain, ![X17, X18]:k4_xboole_0(X17,X18)=k5_xboole_0(X17,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.52/0.72  cnf(c_0_54, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.52/0.72  cnf(c_0_55, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.52/0.72  cnf(c_0_56, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.52/0.72  cnf(c_0_57, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.52/0.72  cnf(c_0_58, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(X1,X2,esk6_0),X1),esk6_0)|~r2_hidden(X1,k9_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_47, c_0_29])).
% 0.52/0.72  cnf(c_0_59, negated_conjecture, (k9_relat_1(esk6_0,k1_relat_1(esk6_0))=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_29])).
% 0.52/0.72  cnf(c_0_60, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),k2_relat_1(esk6_0))|~r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_42, c_0_49])).
% 0.52/0.72  cnf(c_0_61, negated_conjecture, (r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),esk5_0)|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_35, c_0_40])).
% 0.52/0.72  cnf(c_0_62, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)|r2_hidden(esk1_2(esk5_0,X1),X1)|~r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.52/0.72  cnf(c_0_63, negated_conjecture, (r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),k2_relat_1(esk6_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_41])).
% 0.52/0.72  cnf(c_0_64, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))|r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_52, c_0_49])).
% 0.52/0.72  cnf(c_0_65, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)|r2_hidden(esk1_2(esk5_0,X1),esk5_0)|~r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_42, c_0_51])).
% 0.52/0.72  fof(c_0_66, plain, ![X41, X42, X43]:(((r2_hidden(X41,X42)|~r2_hidden(X41,k4_xboole_0(X42,k1_tarski(X43))))&(X41!=X43|~r2_hidden(X41,k4_xboole_0(X42,k1_tarski(X43)))))&(~r2_hidden(X41,X42)|X41=X43|r2_hidden(X41,k4_xboole_0(X42,k1_tarski(X43))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.52/0.72  fof(c_0_67, plain, ![X20]:k2_tarski(X20,X20)=k1_tarski(X20), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.52/0.72  cnf(c_0_68, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.52/0.72  cnf(c_0_69, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.52/0.72  fof(c_0_70, plain, ![X23, X24, X25]:k2_enumset1(X23,X23,X24,X25)=k1_enumset1(X23,X24,X25), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.52/0.72  fof(c_0_71, plain, ![X26, X27, X28, X29]:k3_enumset1(X26,X26,X27,X28,X29)=k2_enumset1(X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.52/0.72  fof(c_0_72, plain, ![X30, X31, X32, X33, X34]:k4_enumset1(X30,X30,X31,X32,X33,X34)=k3_enumset1(X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.52/0.72  fof(c_0_73, plain, ![X35, X36, X37, X38, X39, X40]:k5_enumset1(X35,X35,X36,X37,X38,X39,X40)=k4_enumset1(X35,X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.52/0.72  cnf(c_0_74, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_56, c_0_57])).
% 0.52/0.72  cnf(c_0_75, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(X1,k1_relat_1(esk6_0),esk6_0),X1),esk6_0)|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.52/0.72  cnf(c_0_76, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.52/0.72  cnf(c_0_77, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),k2_relat_1(esk6_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.52/0.72  cnf(c_0_78, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0)|r2_hidden(esk1_2(X1,k2_relat_1(esk6_0)),X1)|~r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1)), inference(spm,[status(thm)],[c_0_42, c_0_64])).
% 0.52/0.72  cnf(c_0_79, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0)|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_65, c_0_63])).
% 0.52/0.72  cnf(c_0_80, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.52/0.72  cnf(c_0_81, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.52/0.72  cnf(c_0_82, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.52/0.72  cnf(c_0_83, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.52/0.72  cnf(c_0_84, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.52/0.72  cnf(c_0_85, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.52/0.72  cnf(c_0_86, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.52/0.72  fof(c_0_87, plain, ![X19]:k4_xboole_0(k1_xboole_0,X19)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.52/0.72  cnf(c_0_88, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk6_0,X2))|~r2_hidden(k4_tarski(X1,X3),esk6_0)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_74, c_0_29])).
% 0.52/0.72  cnf(c_0_89, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),esk1_2(k2_relat_1(esk6_0),esk5_0)),esk6_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.52/0.72  cnf(c_0_90, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)|r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),X1)|~r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),X1)), inference(spm,[status(thm)],[c_0_50, c_0_77])).
% 0.52/0.72  cnf(c_0_91, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.52/0.72  cnf(c_0_92, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k5_enumset1(X3,X3,X3,X3,X3,X3,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81]), c_0_55]), c_0_82]), c_0_83]), c_0_83]), c_0_84]), c_0_84]), c_0_85]), c_0_85]), c_0_86]), c_0_86])).
% 0.52/0.72  cnf(c_0_93, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.52/0.72  cnf(c_0_94, negated_conjecture, (r2_hidden(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),k10_relat_1(esk6_0,X1))|~r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.52/0.72  cnf(c_0_95, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.52/0.72  cnf(c_0_96, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k5_enumset1(X2,X2,X2,X2,X2,X2,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))))), inference(er,[status(thm)],[c_0_92])).
% 0.52/0.72  cnf(c_0_97, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_82]), c_0_83]), c_0_84]), c_0_85]), c_0_86])).
% 0.52/0.72  cnf(c_0_98, negated_conjecture, (r2_hidden(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),k10_relat_1(esk6_0,esk5_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.52/0.72  cnf(c_0_99, negated_conjecture, (k10_relat_1(esk6_0,esk5_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.52/0.72  cnf(c_0_100, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.52/0.72  cnf(c_0_101, negated_conjecture, (r1_xboole_0(k2_relat_1(esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100])).
% 0.52/0.72  cnf(c_0_102, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),X1)|~r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1)), inference(spm,[status(thm)],[c_0_50, c_0_95])).
% 0.52/0.72  cnf(c_0_103, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk6_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_34, c_0_101])).
% 0.52/0.72  cnf(c_0_104, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_102, c_0_76])).
% 0.52/0.72  cnf(c_0_105, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_91])]), ['proof']).
% 0.52/0.72  # SZS output end CNFRefutation
% 0.52/0.72  # Proof object total steps             : 106
% 0.52/0.72  # Proof object clause steps            : 69
% 0.52/0.72  # Proof object formula steps           : 37
% 0.52/0.72  # Proof object conjectures             : 41
% 0.52/0.72  # Proof object clause conjectures      : 38
% 0.52/0.72  # Proof object formula conjectures     : 3
% 0.52/0.72  # Proof object initial clauses used    : 24
% 0.52/0.72  # Proof object initial formulas used   : 18
% 0.52/0.72  # Proof object generating inferences   : 39
% 0.52/0.72  # Proof object simplifying inferences  : 23
% 0.52/0.72  # Training examples: 0 positive, 0 negative
% 0.52/0.72  # Parsed axioms                        : 18
% 0.52/0.72  # Removed by relevancy pruning/SinE    : 0
% 0.52/0.72  # Initial clauses                      : 31
% 0.52/0.72  # Removed in clause preprocessing      : 8
% 0.52/0.72  # Initial clauses in saturation        : 23
% 0.52/0.72  # Processed clauses                    : 1922
% 0.52/0.72  # ...of these trivial                  : 61
% 0.52/0.72  # ...subsumed                          : 929
% 0.52/0.72  # ...remaining for further processing  : 932
% 0.52/0.72  # Other redundant clauses eliminated   : 12
% 0.52/0.72  # Clauses deleted for lack of memory   : 0
% 0.52/0.72  # Backward-subsumed                    : 11
% 0.52/0.72  # Backward-rewritten                   : 118
% 0.52/0.72  # Generated clauses                    : 37798
% 0.52/0.72  # ...of the previous two non-trivial   : 21677
% 0.52/0.72  # Contextual simplify-reflections      : 5
% 0.52/0.72  # Paramodulations                      : 37776
% 0.52/0.72  # Factorizations                       : 10
% 0.52/0.72  # Equation resolutions                 : 12
% 0.52/0.72  # Propositional unsat checks           : 0
% 0.52/0.72  #    Propositional check models        : 0
% 0.52/0.72  #    Propositional check unsatisfiable : 0
% 0.52/0.72  #    Propositional clauses             : 0
% 0.52/0.72  #    Propositional clauses after purity: 0
% 0.52/0.72  #    Propositional unsat core size     : 0
% 0.52/0.72  #    Propositional preprocessing time  : 0.000
% 0.52/0.72  #    Propositional encoding time       : 0.000
% 0.52/0.72  #    Propositional solver time         : 0.000
% 0.52/0.72  #    Success case prop preproc time    : 0.000
% 0.52/0.72  #    Success case prop encoding time   : 0.000
% 0.52/0.72  #    Success case prop solver time     : 0.000
% 0.52/0.72  # Current number of processed clauses  : 779
% 0.52/0.72  #    Positive orientable unit clauses  : 120
% 0.52/0.72  #    Positive unorientable unit clauses: 0
% 0.52/0.72  #    Negative unit clauses             : 3
% 0.52/0.72  #    Non-unit-clauses                  : 656
% 0.52/0.72  # Current number of unprocessed clauses: 19511
% 0.52/0.72  # ...number of literals in the above   : 68969
% 0.52/0.72  # Current number of archived formulas  : 0
% 0.52/0.72  # Current number of archived clauses   : 160
% 0.52/0.72  # Clause-clause subsumption calls (NU) : 56317
% 0.52/0.72  # Rec. Clause-clause subsumption calls : 48098
% 0.52/0.72  # Non-unit clause-clause subsumptions  : 919
% 0.52/0.72  # Unit Clause-clause subsumption calls : 460
% 0.52/0.72  # Rewrite failures with RHS unbound    : 0
% 0.52/0.72  # BW rewrite match attempts            : 129
% 0.52/0.72  # BW rewrite match successes           : 9
% 0.52/0.72  # Condensation attempts                : 0
% 0.52/0.72  # Condensation successes               : 0
% 0.52/0.72  # Termbank termtop insertions          : 798108
% 0.52/0.72  
% 0.52/0.72  # -------------------------------------------------
% 0.52/0.72  # User time                : 0.356 s
% 0.52/0.72  # System time              : 0.020 s
% 0.52/0.72  # Total time               : 0.376 s
% 0.52/0.72  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
