%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:38 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 448 expanded)
%              Number of clauses        :   61 ( 200 expanded)
%              Number of leaves         :   18 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          :  223 (1456 expanded)
%              Number of equality atoms :   51 ( 247 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

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

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

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
    ! [X14] :
      ( X14 = k1_xboole_0
      | r2_hidden(esk2_1(X14),X14) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_21,plain,(
    ! [X58,X59,X60,X62] :
      ( ( r2_hidden(esk4_3(X58,X59,X60),k2_relat_1(X60))
        | ~ r2_hidden(X58,k10_relat_1(X60,X59))
        | ~ v1_relat_1(X60) )
      & ( r2_hidden(k4_tarski(X58,esk4_3(X58,X59,X60)),X60)
        | ~ r2_hidden(X58,k10_relat_1(X60,X59))
        | ~ v1_relat_1(X60) )
      & ( r2_hidden(esk4_3(X58,X59,X60),X59)
        | ~ r2_hidden(X58,k10_relat_1(X60,X59))
        | ~ v1_relat_1(X60) )
      & ( ~ r2_hidden(X62,k2_relat_1(X60))
        | ~ r2_hidden(k4_tarski(X58,X62),X60)
        | ~ r2_hidden(X62,X59)
        | r2_hidden(X58,k10_relat_1(X60,X59))
        | ~ v1_relat_1(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_22,negated_conjecture,
    ( k10_relat_1(esk6_0,esk5_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_25,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))
    | ~ r1_xboole_0(k2_relat_1(esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X52,X53,X54,X56] :
      ( ( r2_hidden(esk3_3(X52,X53,X54),k1_relat_1(X54))
        | ~ r2_hidden(X52,k9_relat_1(X54,X53))
        | ~ v1_relat_1(X54) )
      & ( r2_hidden(k4_tarski(esk3_3(X52,X53,X54),X52),X54)
        | ~ r2_hidden(X52,k9_relat_1(X54,X53))
        | ~ v1_relat_1(X54) )
      & ( r2_hidden(esk3_3(X52,X53,X54),X53)
        | ~ r2_hidden(X52,k9_relat_1(X54,X53))
        | ~ v1_relat_1(X54) )
      & ( ~ r2_hidden(X56,k1_relat_1(X54))
        | ~ r2_hidden(k4_tarski(X56,X52),X54)
        | ~ r2_hidden(X56,X53)
        | r2_hidden(X52,k9_relat_1(X54,X53))
        | ~ v1_relat_1(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_30,plain,(
    ! [X57] :
      ( ~ v1_relat_1(X57)
      | k9_relat_1(X57,k1_relat_1(X57)) = k2_relat_1(X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_3(X1,X2,esk6_0),k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,k10_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_35,plain,(
    ! [X50,X51] : k1_setfam_1(k2_tarski(X50,X51)) = k3_xboole_0(X50,X51) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_36,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_37,plain,(
    ! [X63,X64,X65] :
      ( ( r2_hidden(X63,k1_relat_1(X65))
        | ~ r2_hidden(k4_tarski(X63,X64),X65)
        | ~ v1_relat_1(X65) )
      & ( r2_hidden(X64,k2_relat_1(X65))
        | ~ r2_hidden(k4_tarski(X63,X64),X65)
        | ~ v1_relat_1(X65) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),k2_relat_1(esk6_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_3(X1,X2,esk6_0),X2)
    | ~ r2_hidden(X1,k10_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_44,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,esk6_0),X1),esk6_0)
    | ~ r2_hidden(X1,k9_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_26])).

cnf(c_0_50,negated_conjecture,
    ( k9_relat_1(esk6_0,k1_relat_1(esk6_0)) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_26])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),k2_relat_1(esk6_0))
    | ~ r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),esk5_0)
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_33])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_43])).

fof(c_0_54,plain,(
    ! [X47,X48,X49] :
      ( ( r2_hidden(X47,X48)
        | ~ r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49))) )
      & ( X47 != X49
        | ~ r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49))) )
      & ( ~ r2_hidden(X47,X48)
        | X47 = X49
        | r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_55,plain,(
    ! [X19] : k2_tarski(X19,X19) = k1_tarski(X19) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_58,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_59,plain,(
    ! [X25,X26,X27,X28] : k3_enumset1(X25,X25,X26,X27,X28) = k2_enumset1(X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_60,plain,(
    ! [X29,X30,X31,X32,X33] : k4_enumset1(X29,X29,X30,X31,X32,X33) = k3_enumset1(X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_61,plain,(
    ! [X34,X35,X36,X37,X38,X39] : k5_enumset1(X34,X34,X35,X36,X37,X38,X39) = k4_enumset1(X34,X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_62,plain,(
    ! [X40,X41,X42,X43,X44,X45,X46] : k6_enumset1(X40,X40,X41,X42,X43,X44,X45,X46) = k5_enumset1(X40,X41,X42,X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(X1,k1_relat_1(esk6_0),esk6_0),X1),esk6_0)
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_66,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_43])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),esk5_0)
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_53])).

cnf(c_0_68,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_69,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_71,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_73,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_75,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_76,plain,(
    ! [X18] : k4_xboole_0(k1_xboole_0,X18) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk6_0,X2))
    | ~ r2_hidden(k4_tarski(X1,X3),esk6_0)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_26])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),esk1_2(k2_relat_1(esk6_0),esk5_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)
    | r2_hidden(esk1_2(X1,esk5_0),esk5_0)
    | ~ r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),k2_relat_1(esk6_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_53])).

cnf(c_0_81,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_46]),c_0_70]),c_0_71]),c_0_71]),c_0_72]),c_0_72]),c_0_73]),c_0_73]),c_0_74]),c_0_74]),c_0_75]),c_0_75])).

cnf(c_0_82,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),k10_relat_1(esk6_0,X1))
    | ~ r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_70]),c_0_71]),c_0_72]),c_0_73]),c_0_74]),c_0_75])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),k10_relat_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( k10_relat_1(esk6_0,esk5_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_89,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),X1)
    | ~ r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))
    | r2_hidden(esk1_2(esk5_0,X1),esk5_0)
    | ~ r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_52])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),esk5_0)
    | ~ r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_84])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_65])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_41]),c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:04:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.46/0.68  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.46/0.68  # and selection function SelectNegativeLiterals.
% 0.46/0.68  #
% 0.46/0.68  # Preprocessing time       : 0.028 s
% 0.46/0.68  # Presaturation interreduction done
% 0.46/0.68  
% 0.46/0.68  # Proof found!
% 0.46/0.68  # SZS status Theorem
% 0.46/0.68  # SZS output start CNFRefutation
% 0.46/0.68  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.46/0.68  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.46/0.68  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.46/0.68  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.46/0.68  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.46/0.68  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.46/0.68  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.46/0.68  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.46/0.68  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 0.46/0.68  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.46/0.68  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.46/0.68  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.46/0.68  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.46/0.68  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.46/0.68  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.46/0.68  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.46/0.68  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.46/0.68  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.46/0.68  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.46/0.68  fof(c_0_19, negated_conjecture, (v1_relat_1(esk6_0)&((k10_relat_1(esk6_0,esk5_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk6_0),esk5_0))&(k10_relat_1(esk6_0,esk5_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk6_0),esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.46/0.68  fof(c_0_20, plain, ![X14]:(X14=k1_xboole_0|r2_hidden(esk2_1(X14),X14)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.46/0.68  fof(c_0_21, plain, ![X58, X59, X60, X62]:((((r2_hidden(esk4_3(X58,X59,X60),k2_relat_1(X60))|~r2_hidden(X58,k10_relat_1(X60,X59))|~v1_relat_1(X60))&(r2_hidden(k4_tarski(X58,esk4_3(X58,X59,X60)),X60)|~r2_hidden(X58,k10_relat_1(X60,X59))|~v1_relat_1(X60)))&(r2_hidden(esk4_3(X58,X59,X60),X59)|~r2_hidden(X58,k10_relat_1(X60,X59))|~v1_relat_1(X60)))&(~r2_hidden(X62,k2_relat_1(X60))|~r2_hidden(k4_tarski(X58,X62),X60)|~r2_hidden(X62,X59)|r2_hidden(X58,k10_relat_1(X60,X59))|~v1_relat_1(X60))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.46/0.68  cnf(c_0_22, negated_conjecture, (k10_relat_1(esk6_0,esk5_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.68  cnf(c_0_23, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.46/0.68  fof(c_0_24, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk1_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk1_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.46/0.68  cnf(c_0_25, plain, (r2_hidden(esk4_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.46/0.68  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.68  cnf(c_0_27, negated_conjecture, (r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))|~r1_xboole_0(k2_relat_1(esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.46/0.68  cnf(c_0_28, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.46/0.68  fof(c_0_29, plain, ![X52, X53, X54, X56]:((((r2_hidden(esk3_3(X52,X53,X54),k1_relat_1(X54))|~r2_hidden(X52,k9_relat_1(X54,X53))|~v1_relat_1(X54))&(r2_hidden(k4_tarski(esk3_3(X52,X53,X54),X52),X54)|~r2_hidden(X52,k9_relat_1(X54,X53))|~v1_relat_1(X54)))&(r2_hidden(esk3_3(X52,X53,X54),X53)|~r2_hidden(X52,k9_relat_1(X54,X53))|~v1_relat_1(X54)))&(~r2_hidden(X56,k1_relat_1(X54))|~r2_hidden(k4_tarski(X56,X52),X54)|~r2_hidden(X56,X53)|r2_hidden(X52,k9_relat_1(X54,X53))|~v1_relat_1(X54))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.46/0.68  fof(c_0_30, plain, ![X57]:(~v1_relat_1(X57)|k9_relat_1(X57,k1_relat_1(X57))=k2_relat_1(X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.46/0.68  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.46/0.68  cnf(c_0_32, negated_conjecture, (r2_hidden(esk4_3(X1,X2,esk6_0),k2_relat_1(esk6_0))|~r2_hidden(X1,k10_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.46/0.68  cnf(c_0_33, negated_conjecture, (r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.46/0.68  cnf(c_0_34, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.46/0.68  fof(c_0_35, plain, ![X50, X51]:k1_setfam_1(k2_tarski(X50,X51))=k3_xboole_0(X50,X51), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.46/0.68  fof(c_0_36, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.46/0.68  fof(c_0_37, plain, ![X63, X64, X65]:((r2_hidden(X63,k1_relat_1(X65))|~r2_hidden(k4_tarski(X63,X64),X65)|~v1_relat_1(X65))&(r2_hidden(X64,k2_relat_1(X65))|~r2_hidden(k4_tarski(X63,X64),X65)|~v1_relat_1(X65))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.46/0.68  cnf(c_0_38, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.46/0.68  cnf(c_0_39, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.46/0.68  cnf(c_0_40, plain, (r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_31, c_0_28])).
% 0.46/0.68  cnf(c_0_41, negated_conjecture, (r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),k2_relat_1(esk6_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.46/0.68  cnf(c_0_42, negated_conjecture, (r2_hidden(esk4_3(X1,X2,esk6_0),X2)|~r2_hidden(X1,k10_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_34, c_0_26])).
% 0.46/0.68  cnf(c_0_43, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.46/0.68  fof(c_0_44, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.46/0.68  cnf(c_0_45, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.46/0.68  cnf(c_0_46, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.46/0.68  cnf(c_0_47, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.46/0.68  cnf(c_0_48, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.46/0.68  cnf(c_0_49, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(X1,X2,esk6_0),X1),esk6_0)|~r2_hidden(X1,k9_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_38, c_0_26])).
% 0.46/0.68  cnf(c_0_50, negated_conjecture, (k9_relat_1(esk6_0,k1_relat_1(esk6_0))=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_26])).
% 0.46/0.68  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),k2_relat_1(esk6_0))|~r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.46/0.68  cnf(c_0_52, negated_conjecture, (r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),esk5_0)|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_42, c_0_33])).
% 0.46/0.68  cnf(c_0_53, negated_conjecture, (r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_43])).
% 0.46/0.68  fof(c_0_54, plain, ![X47, X48, X49]:(((r2_hidden(X47,X48)|~r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49))))&(X47!=X49|~r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49)))))&(~r2_hidden(X47,X48)|X47=X49|r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.46/0.68  fof(c_0_55, plain, ![X19]:k2_tarski(X19,X19)=k1_tarski(X19), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.46/0.68  cnf(c_0_56, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.46/0.68  cnf(c_0_57, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.46/0.68  fof(c_0_58, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.46/0.68  fof(c_0_59, plain, ![X25, X26, X27, X28]:k3_enumset1(X25,X25,X26,X27,X28)=k2_enumset1(X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.46/0.68  fof(c_0_60, plain, ![X29, X30, X31, X32, X33]:k4_enumset1(X29,X29,X30,X31,X32,X33)=k3_enumset1(X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.46/0.68  fof(c_0_61, plain, ![X34, X35, X36, X37, X38, X39]:k5_enumset1(X34,X34,X35,X36,X37,X38,X39)=k4_enumset1(X34,X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.46/0.68  fof(c_0_62, plain, ![X40, X41, X42, X43, X44, X45, X46]:k6_enumset1(X40,X40,X41,X42,X43,X44,X45,X46)=k5_enumset1(X40,X41,X42,X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.46/0.68  cnf(c_0_63, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_47, c_0_48])).
% 0.46/0.68  cnf(c_0_64, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(X1,k1_relat_1(esk6_0),esk6_0),X1),esk6_0)|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.46/0.68  cnf(c_0_65, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.46/0.68  cnf(c_0_66, plain, (r2_hidden(esk1_2(X1,X2),X2)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_31, c_0_43])).
% 0.46/0.68  cnf(c_0_67, negated_conjecture, (r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),esk5_0)|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_53])).
% 0.46/0.68  cnf(c_0_68, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.46/0.68  cnf(c_0_69, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.46/0.68  cnf(c_0_70, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.46/0.68  cnf(c_0_71, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.46/0.68  cnf(c_0_72, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.46/0.68  cnf(c_0_73, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.46/0.68  cnf(c_0_74, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.46/0.68  cnf(c_0_75, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.46/0.68  fof(c_0_76, plain, ![X18]:k4_xboole_0(k1_xboole_0,X18)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.46/0.68  cnf(c_0_77, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk6_0,X2))|~r2_hidden(k4_tarski(X1,X3),esk6_0)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_63, c_0_26])).
% 0.46/0.68  cnf(c_0_78, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),esk1_2(k2_relat_1(esk6_0),esk5_0)),esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.46/0.68  cnf(c_0_79, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)|r2_hidden(esk1_2(X1,esk5_0),esk5_0)|~r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.46/0.68  cnf(c_0_80, negated_conjecture, (r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),k2_relat_1(esk6_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_53])).
% 0.46/0.68  cnf(c_0_81, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_46]), c_0_70]), c_0_71]), c_0_71]), c_0_72]), c_0_72]), c_0_73]), c_0_73]), c_0_74]), c_0_74]), c_0_75]), c_0_75])).
% 0.46/0.68  cnf(c_0_82, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.46/0.68  cnf(c_0_83, negated_conjecture, (r2_hidden(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),k10_relat_1(esk6_0,X1))|~r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.46/0.68  cnf(c_0_84, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.46/0.68  cnf(c_0_85, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))), inference(er,[status(thm)],[c_0_81])).
% 0.46/0.68  cnf(c_0_86, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_70]), c_0_71]), c_0_72]), c_0_73]), c_0_74]), c_0_75])).
% 0.46/0.68  cnf(c_0_87, negated_conjecture, (r2_hidden(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),k10_relat_1(esk6_0,esk5_0))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.46/0.68  cnf(c_0_88, negated_conjecture, (k10_relat_1(esk6_0,esk5_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.68  cnf(c_0_89, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.46/0.68  cnf(c_0_90, negated_conjecture, (r1_xboole_0(k2_relat_1(esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])).
% 0.46/0.68  cnf(c_0_91, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),X1)|~r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1)), inference(spm,[status(thm)],[c_0_66, c_0_84])).
% 0.46/0.68  cnf(c_0_92, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))|r2_hidden(esk1_2(esk5_0,X1),esk5_0)|~r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_40, c_0_52])).
% 0.46/0.68  cnf(c_0_93, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),esk5_0)|~r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1)), inference(spm,[status(thm)],[c_0_40, c_0_84])).
% 0.46/0.68  cnf(c_0_94, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk6_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_31, c_0_90])).
% 0.46/0.68  cnf(c_0_95, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_91, c_0_65])).
% 0.46/0.68  cnf(c_0_96, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_41]), c_0_93])).
% 0.46/0.68  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96])]), ['proof']).
% 0.46/0.68  # SZS output end CNFRefutation
% 0.46/0.68  # Proof object total steps             : 98
% 0.46/0.68  # Proof object clause steps            : 61
% 0.46/0.68  # Proof object formula steps           : 37
% 0.46/0.68  # Proof object conjectures             : 34
% 0.46/0.68  # Proof object clause conjectures      : 31
% 0.46/0.68  # Proof object formula conjectures     : 3
% 0.46/0.68  # Proof object initial clauses used    : 24
% 0.46/0.68  # Proof object initial formulas used   : 18
% 0.46/0.68  # Proof object generating inferences   : 31
% 0.46/0.68  # Proof object simplifying inferences  : 27
% 0.46/0.68  # Training examples: 0 positive, 0 negative
% 0.46/0.68  # Parsed axioms                        : 18
% 0.46/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.68  # Initial clauses                      : 31
% 0.46/0.68  # Removed in clause preprocessing      : 9
% 0.46/0.68  # Initial clauses in saturation        : 22
% 0.46/0.68  # Processed clauses                    : 1743
% 0.46/0.68  # ...of these trivial                  : 81
% 0.46/0.68  # ...subsumed                          : 773
% 0.46/0.68  # ...remaining for further processing  : 889
% 0.46/0.68  # Other redundant clauses eliminated   : 14
% 0.46/0.68  # Clauses deleted for lack of memory   : 0
% 0.46/0.68  # Backward-subsumed                    : 17
% 0.46/0.68  # Backward-rewritten                   : 96
% 0.46/0.68  # Generated clauses                    : 33902
% 0.46/0.68  # ...of the previous two non-trivial   : 18579
% 0.46/0.68  # Contextual simplify-reflections      : 6
% 0.46/0.68  # Paramodulations                      : 33876
% 0.46/0.68  # Factorizations                       : 12
% 0.46/0.68  # Equation resolutions                 : 14
% 0.46/0.68  # Propositional unsat checks           : 0
% 0.46/0.68  #    Propositional check models        : 0
% 0.46/0.68  #    Propositional check unsatisfiable : 0
% 0.46/0.68  #    Propositional clauses             : 0
% 0.46/0.68  #    Propositional clauses after purity: 0
% 0.46/0.68  #    Propositional unsat core size     : 0
% 0.46/0.68  #    Propositional preprocessing time  : 0.000
% 0.46/0.68  #    Propositional encoding time       : 0.000
% 0.46/0.68  #    Propositional solver time         : 0.000
% 0.46/0.68  #    Success case prop preproc time    : 0.000
% 0.46/0.68  #    Success case prop encoding time   : 0.000
% 0.46/0.68  #    Success case prop solver time     : 0.000
% 0.46/0.68  # Current number of processed clauses  : 753
% 0.46/0.68  #    Positive orientable unit clauses  : 118
% 0.46/0.68  #    Positive unorientable unit clauses: 0
% 0.46/0.68  #    Negative unit clauses             : 3
% 0.46/0.68  #    Non-unit-clauses                  : 632
% 0.46/0.68  # Current number of unprocessed clauses: 16490
% 0.46/0.68  # ...number of literals in the above   : 60246
% 0.46/0.68  # Current number of archived formulas  : 0
% 0.46/0.68  # Current number of archived clauses   : 144
% 0.46/0.68  # Clause-clause subsumption calls (NU) : 29866
% 0.46/0.68  # Rec. Clause-clause subsumption calls : 26335
% 0.46/0.68  # Non-unit clause-clause subsumptions  : 772
% 0.46/0.68  # Unit Clause-clause subsumption calls : 180
% 0.46/0.68  # Rewrite failures with RHS unbound    : 0
% 0.46/0.68  # BW rewrite match attempts            : 127
% 0.46/0.68  # BW rewrite match successes           : 7
% 0.46/0.68  # Condensation attempts                : 0
% 0.46/0.68  # Condensation successes               : 0
% 0.46/0.68  # Termbank termtop insertions          : 710419
% 0.46/0.68  
% 0.46/0.68  # -------------------------------------------------
% 0.46/0.68  # User time                : 0.337 s
% 0.46/0.68  # System time              : 0.010 s
% 0.46/0.68  # Total time               : 0.347 s
% 0.46/0.68  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
