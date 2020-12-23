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
% DateTime   : Thu Dec  3 10:51:37 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 436 expanded)
%              Number of clauses        :   59 ( 196 expanded)
%              Number of leaves         :   16 ( 107 expanded)
%              Depth                    :   14
%              Number of atoms          :  202 (1426 expanded)
%              Number of equality atoms :   54 ( 247 expanded)
%              Maximal formula depth    :   15 (   4 average)
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

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & ( k10_relat_1(esk8_0,esk7_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk8_0),esk7_0) )
    & ( k10_relat_1(esk8_0,esk7_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk8_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_18,plain,(
    ! [X14] :
      ( X14 = k1_xboole_0
      | r2_hidden(esk2_1(X14),X14) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_19,plain,(
    ! [X63,X64,X65,X67] :
      ( ( r2_hidden(esk6_3(X63,X64,X65),k2_relat_1(X65))
        | ~ r2_hidden(X63,k10_relat_1(X65,X64))
        | ~ v1_relat_1(X65) )
      & ( r2_hidden(k4_tarski(X63,esk6_3(X63,X64,X65)),X65)
        | ~ r2_hidden(X63,k10_relat_1(X65,X64))
        | ~ v1_relat_1(X65) )
      & ( r2_hidden(esk6_3(X63,X64,X65),X64)
        | ~ r2_hidden(X63,k10_relat_1(X65,X64))
        | ~ v1_relat_1(X65) )
      & ( ~ r2_hidden(X67,k2_relat_1(X65))
        | ~ r2_hidden(k4_tarski(X63,X67),X65)
        | ~ r2_hidden(X67,X64)
        | r2_hidden(X63,k10_relat_1(X65,X64))
        | ~ v1_relat_1(X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_20,negated_conjecture,
    ( k10_relat_1(esk8_0,esk7_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk2_1(k10_relat_1(esk8_0,esk7_0)),k10_relat_1(esk8_0,esk7_0))
    | ~ r1_xboole_0(k2_relat_1(esk8_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X52,X53,X54,X56,X57,X58,X59,X61] :
      ( ( ~ r2_hidden(X54,X53)
        | r2_hidden(k4_tarski(esk3_3(X52,X53,X54),X54),X52)
        | X53 != k2_relat_1(X52) )
      & ( ~ r2_hidden(k4_tarski(X57,X56),X52)
        | r2_hidden(X56,X53)
        | X53 != k2_relat_1(X52) )
      & ( ~ r2_hidden(esk4_2(X58,X59),X59)
        | ~ r2_hidden(k4_tarski(X61,esk4_2(X58,X59)),X58)
        | X59 = k2_relat_1(X58) )
      & ( r2_hidden(esk4_2(X58,X59),X59)
        | r2_hidden(k4_tarski(esk5_2(X58,X59),esk4_2(X58,X59)),X58)
        | X59 = k2_relat_1(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk6_3(X1,X2,esk8_0),k2_relat_1(esk8_0))
    | ~ r2_hidden(X1,k10_relat_1(esk8_0,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk2_1(k10_relat_1(esk8_0,esk7_0)),k10_relat_1(esk8_0,esk7_0))
    | r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_32,plain,(
    ! [X50,X51] : k1_setfam_1(k2_tarski(X50,X51)) = k3_xboole_0(X50,X51) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_33,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_34,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk6_3(esk2_1(k10_relat_1(esk8_0,esk7_0)),esk7_0,esk8_0),k2_relat_1(esk8_0))
    | r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk6_3(X1,X2,esk8_0),X2)
    | ~ r2_hidden(X1,k10_relat_1(esk8_0,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_24])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_39,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_40,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(esk3_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),k2_relat_1(esk8_0))
    | r2_hidden(esk1_2(k2_relat_1(esk8_0),X1),k2_relat_1(esk8_0))
    | ~ r2_hidden(esk6_3(esk2_1(k10_relat_1(esk8_0,esk7_0)),esk7_0,esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk6_3(esk2_1(k10_relat_1(esk8_0,esk7_0)),esk7_0,esk8_0),esk7_0)
    | r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk2_1(k10_relat_1(esk8_0,esk7_0)),k10_relat_1(esk8_0,esk7_0))
    | r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_38])).

fof(c_0_48,plain,(
    ! [X47,X48,X49] :
      ( ( r2_hidden(X47,X48)
        | ~ r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49))) )
      & ( X47 != X49
        | ~ r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49))) )
      & ( ~ r2_hidden(X47,X48)
        | X47 = X49
        | r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_49,plain,(
    ! [X19] : k2_tarski(X19,X19) = k1_tarski(X19) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_52,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_53,plain,(
    ! [X25,X26,X27,X28] : k3_enumset1(X25,X25,X26,X27,X28) = k2_enumset1(X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_54,plain,(
    ! [X29,X30,X31,X32,X33] : k4_enumset1(X29,X29,X30,X31,X32,X33) = k3_enumset1(X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_55,plain,(
    ! [X34,X35,X36,X37,X38,X39] : k5_enumset1(X34,X34,X35,X36,X37,X38,X39) = k4_enumset1(X34,X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_56,plain,(
    ! [X40,X41,X42,X43,X44,X45,X46] : k6_enumset1(X40,X40,X41,X42,X43,X44,X45,X46) = k5_enumset1(X40,X41,X42,X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_58,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk6_3(esk2_1(k10_relat_1(esk8_0,esk7_0)),esk7_0,esk8_0),esk7_0)
    | r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_47])).

cnf(c_0_62,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_65,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_66,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_68,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_69,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_70,plain,(
    ! [X18] : k4_xboole_0(k1_xboole_0,X18) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk8_0,X2))
    | ~ r2_hidden(k4_tarski(X1,X3),esk8_0)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_24])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(esk8_0,k2_relat_1(esk8_0),esk1_2(k2_relat_1(esk8_0),esk7_0)),esk1_2(k2_relat_1(esk8_0),esk7_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),esk7_0)
    | r2_hidden(esk1_2(X1,esk7_0),esk7_0)
    | ~ r2_hidden(esk6_3(esk2_1(k10_relat_1(esk8_0,esk7_0)),esk7_0,esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk6_3(esk2_1(k10_relat_1(esk8_0,esk7_0)),esk7_0,esk8_0),k2_relat_1(esk8_0))
    | r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_47])).

cnf(c_0_75,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_41]),c_0_64]),c_0_65]),c_0_65]),c_0_66]),c_0_66]),c_0_67]),c_0_67]),c_0_68]),c_0_68]),c_0_69]),c_0_69])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk3_3(esk8_0,k2_relat_1(esk8_0),esk1_2(k2_relat_1(esk8_0),esk7_0)),k10_relat_1(esk8_0,X1))
    | ~ r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_80,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_64]),c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_69])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk3_3(esk8_0,k2_relat_1(esk8_0),esk1_2(k2_relat_1(esk8_0),esk7_0)),k10_relat_1(esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( k10_relat_1(esk8_0,esk7_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_83,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk8_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,X1),X1)
    | ~ r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),k2_relat_1(esk8_0))
    | r2_hidden(esk1_2(esk7_0,X1),esk7_0)
    | ~ r2_hidden(esk6_3(esk2_1(k10_relat_1(esk8_0,esk7_0)),esk7_0,esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_46])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,X1),esk7_0)
    | ~ r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk8_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,k2_relat_1(esk8_0)),k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_59])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk1_2(esk7_0,k2_relat_1(esk8_0)),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_36]),c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:04:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.62/0.80  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.62/0.80  # and selection function SelectNegativeLiterals.
% 0.62/0.80  #
% 0.62/0.80  # Preprocessing time       : 0.028 s
% 0.62/0.80  # Presaturation interreduction done
% 0.62/0.80  
% 0.62/0.80  # Proof found!
% 0.62/0.80  # SZS status Theorem
% 0.62/0.80  # SZS output start CNFRefutation
% 0.62/0.80  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.62/0.80  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.62/0.80  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.62/0.80  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.62/0.80  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.62/0.80  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.62/0.80  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.62/0.80  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.62/0.80  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.62/0.80  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.62/0.80  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.62/0.80  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.62/0.80  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.62/0.80  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.62/0.80  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.62/0.80  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.62/0.80  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.62/0.80  fof(c_0_17, negated_conjecture, (v1_relat_1(esk8_0)&((k10_relat_1(esk8_0,esk7_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk8_0),esk7_0))&(k10_relat_1(esk8_0,esk7_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk8_0),esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.62/0.80  fof(c_0_18, plain, ![X14]:(X14=k1_xboole_0|r2_hidden(esk2_1(X14),X14)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.62/0.80  fof(c_0_19, plain, ![X63, X64, X65, X67]:((((r2_hidden(esk6_3(X63,X64,X65),k2_relat_1(X65))|~r2_hidden(X63,k10_relat_1(X65,X64))|~v1_relat_1(X65))&(r2_hidden(k4_tarski(X63,esk6_3(X63,X64,X65)),X65)|~r2_hidden(X63,k10_relat_1(X65,X64))|~v1_relat_1(X65)))&(r2_hidden(esk6_3(X63,X64,X65),X64)|~r2_hidden(X63,k10_relat_1(X65,X64))|~v1_relat_1(X65)))&(~r2_hidden(X67,k2_relat_1(X65))|~r2_hidden(k4_tarski(X63,X67),X65)|~r2_hidden(X67,X64)|r2_hidden(X63,k10_relat_1(X65,X64))|~v1_relat_1(X65))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.62/0.80  cnf(c_0_20, negated_conjecture, (k10_relat_1(esk8_0,esk7_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.62/0.80  cnf(c_0_21, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.62/0.80  fof(c_0_22, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk1_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk1_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.62/0.80  cnf(c_0_23, plain, (r2_hidden(esk6_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.62/0.80  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.62/0.80  cnf(c_0_25, negated_conjecture, (r2_hidden(esk2_1(k10_relat_1(esk8_0,esk7_0)),k10_relat_1(esk8_0,esk7_0))|~r1_xboole_0(k2_relat_1(esk8_0),esk7_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.62/0.80  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.62/0.80  fof(c_0_27, plain, ![X52, X53, X54, X56, X57, X58, X59, X61]:(((~r2_hidden(X54,X53)|r2_hidden(k4_tarski(esk3_3(X52,X53,X54),X54),X52)|X53!=k2_relat_1(X52))&(~r2_hidden(k4_tarski(X57,X56),X52)|r2_hidden(X56,X53)|X53!=k2_relat_1(X52)))&((~r2_hidden(esk4_2(X58,X59),X59)|~r2_hidden(k4_tarski(X61,esk4_2(X58,X59)),X58)|X59=k2_relat_1(X58))&(r2_hidden(esk4_2(X58,X59),X59)|r2_hidden(k4_tarski(esk5_2(X58,X59),esk4_2(X58,X59)),X58)|X59=k2_relat_1(X58)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.62/0.80  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.62/0.80  cnf(c_0_29, negated_conjecture, (r2_hidden(esk6_3(X1,X2,esk8_0),k2_relat_1(esk8_0))|~r2_hidden(X1,k10_relat_1(esk8_0,X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.62/0.80  cnf(c_0_30, negated_conjecture, (r2_hidden(esk2_1(k10_relat_1(esk8_0,esk7_0)),k10_relat_1(esk8_0,esk7_0))|r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.62/0.80  cnf(c_0_31, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.62/0.80  fof(c_0_32, plain, ![X50, X51]:k1_setfam_1(k2_tarski(X50,X51))=k3_xboole_0(X50,X51), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.62/0.80  fof(c_0_33, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.62/0.80  cnf(c_0_34, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.62/0.80  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_28, c_0_26])).
% 0.62/0.80  cnf(c_0_36, negated_conjecture, (r2_hidden(esk6_3(esk2_1(k10_relat_1(esk8_0,esk7_0)),esk7_0,esk8_0),k2_relat_1(esk8_0))|r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.62/0.80  cnf(c_0_37, negated_conjecture, (r2_hidden(esk6_3(X1,X2,esk8_0),X2)|~r2_hidden(X1,k10_relat_1(esk8_0,X2))), inference(spm,[status(thm)],[c_0_31, c_0_24])).
% 0.62/0.80  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.62/0.80  fof(c_0_39, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.62/0.80  cnf(c_0_40, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.62/0.80  cnf(c_0_41, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.62/0.80  cnf(c_0_42, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.62/0.80  cnf(c_0_43, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_34])).
% 0.62/0.80  cnf(c_0_44, plain, (r2_hidden(k4_tarski(esk3_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.62/0.80  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),k2_relat_1(esk8_0))|r2_hidden(esk1_2(k2_relat_1(esk8_0),X1),k2_relat_1(esk8_0))|~r2_hidden(esk6_3(esk2_1(k10_relat_1(esk8_0,esk7_0)),esk7_0,esk8_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.62/0.80  cnf(c_0_46, negated_conjecture, (r2_hidden(esk6_3(esk2_1(k10_relat_1(esk8_0,esk7_0)),esk7_0,esk8_0),esk7_0)|r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_37, c_0_30])).
% 0.62/0.80  cnf(c_0_47, negated_conjecture, (r2_hidden(esk2_1(k10_relat_1(esk8_0,esk7_0)),k10_relat_1(esk8_0,esk7_0))|r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_25, c_0_38])).
% 0.62/0.80  fof(c_0_48, plain, ![X47, X48, X49]:(((r2_hidden(X47,X48)|~r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49))))&(X47!=X49|~r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49)))))&(~r2_hidden(X47,X48)|X47=X49|r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.62/0.80  fof(c_0_49, plain, ![X19]:k2_tarski(X19,X19)=k1_tarski(X19), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.62/0.80  cnf(c_0_50, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.62/0.80  cnf(c_0_51, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.62/0.80  fof(c_0_52, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.62/0.80  fof(c_0_53, plain, ![X25, X26, X27, X28]:k3_enumset1(X25,X25,X26,X27,X28)=k2_enumset1(X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.62/0.80  fof(c_0_54, plain, ![X29, X30, X31, X32, X33]:k4_enumset1(X29,X29,X30,X31,X32,X33)=k3_enumset1(X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.62/0.80  fof(c_0_55, plain, ![X34, X35, X36, X37, X38, X39]:k5_enumset1(X34,X34,X35,X36,X37,X38,X39)=k4_enumset1(X34,X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.62/0.80  fof(c_0_56, plain, ![X40, X41, X42, X43, X44, X45, X46]:k6_enumset1(X40,X40,X41,X42,X43,X44,X45,X46)=k5_enumset1(X40,X41,X42,X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.62/0.80  cnf(c_0_57, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_42, c_0_43])).
% 0.62/0.80  cnf(c_0_58, plain, (r2_hidden(k4_tarski(esk3_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_44])).
% 0.62/0.80  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.62/0.80  cnf(c_0_60, plain, (r2_hidden(esk1_2(X1,X2),X2)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_28, c_0_38])).
% 0.62/0.80  cnf(c_0_61, negated_conjecture, (r2_hidden(esk6_3(esk2_1(k10_relat_1(esk8_0,esk7_0)),esk7_0,esk8_0),esk7_0)|r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_47])).
% 0.62/0.80  cnf(c_0_62, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.62/0.80  cnf(c_0_63, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.62/0.80  cnf(c_0_64, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.62/0.80  cnf(c_0_65, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.62/0.80  cnf(c_0_66, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.62/0.80  cnf(c_0_67, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.62/0.80  cnf(c_0_68, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.62/0.80  cnf(c_0_69, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.62/0.80  fof(c_0_70, plain, ![X18]:k4_xboole_0(k1_xboole_0,X18)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.62/0.80  cnf(c_0_71, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk8_0,X2))|~r2_hidden(k4_tarski(X1,X3),esk8_0)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_57, c_0_24])).
% 0.62/0.80  cnf(c_0_72, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(esk8_0,k2_relat_1(esk8_0),esk1_2(k2_relat_1(esk8_0),esk7_0)),esk1_2(k2_relat_1(esk8_0),esk7_0)),esk8_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.62/0.80  cnf(c_0_73, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),esk7_0)|r2_hidden(esk1_2(X1,esk7_0),esk7_0)|~r2_hidden(esk6_3(esk2_1(k10_relat_1(esk8_0,esk7_0)),esk7_0,esk8_0),X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.62/0.80  cnf(c_0_74, negated_conjecture, (r2_hidden(esk6_3(esk2_1(k10_relat_1(esk8_0,esk7_0)),esk7_0,esk8_0),k2_relat_1(esk8_0))|r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_47])).
% 0.62/0.80  cnf(c_0_75, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_41]), c_0_64]), c_0_65]), c_0_65]), c_0_66]), c_0_66]), c_0_67]), c_0_67]), c_0_68]), c_0_68]), c_0_69]), c_0_69])).
% 0.62/0.80  cnf(c_0_76, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.62/0.80  cnf(c_0_77, negated_conjecture, (r2_hidden(esk3_3(esk8_0,k2_relat_1(esk8_0),esk1_2(k2_relat_1(esk8_0),esk7_0)),k10_relat_1(esk8_0,X1))|~r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.62/0.80  cnf(c_0_78, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.62/0.80  cnf(c_0_79, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))), inference(er,[status(thm)],[c_0_75])).
% 0.62/0.80  cnf(c_0_80, plain, (k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_64]), c_0_65]), c_0_66]), c_0_67]), c_0_68]), c_0_69])).
% 0.62/0.80  cnf(c_0_81, negated_conjecture, (r2_hidden(esk3_3(esk8_0,k2_relat_1(esk8_0),esk1_2(k2_relat_1(esk8_0),esk7_0)),k10_relat_1(esk8_0,esk7_0))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.62/0.80  cnf(c_0_82, negated_conjecture, (k10_relat_1(esk8_0,esk7_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.62/0.80  cnf(c_0_83, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.62/0.80  cnf(c_0_84, negated_conjecture, (r1_xboole_0(k2_relat_1(esk8_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])).
% 0.62/0.80  cnf(c_0_85, negated_conjecture, (r2_hidden(esk1_2(esk7_0,X1),X1)|~r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),X1)), inference(spm,[status(thm)],[c_0_60, c_0_78])).
% 0.62/0.80  cnf(c_0_86, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),k2_relat_1(esk8_0))|r2_hidden(esk1_2(esk7_0,X1),esk7_0)|~r2_hidden(esk6_3(esk2_1(k10_relat_1(esk8_0,esk7_0)),esk7_0,esk8_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_46])).
% 0.62/0.80  cnf(c_0_87, negated_conjecture, (r2_hidden(esk1_2(esk7_0,X1),esk7_0)|~r2_hidden(esk1_2(k2_relat_1(esk8_0),esk7_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_78])).
% 0.62/0.80  cnf(c_0_88, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk8_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_28, c_0_84])).
% 0.62/0.80  cnf(c_0_89, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k2_relat_1(esk8_0)),k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_85, c_0_59])).
% 0.62/0.80  cnf(c_0_90, negated_conjecture, (r2_hidden(esk1_2(esk7_0,k2_relat_1(esk8_0)),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_36]), c_0_87])).
% 0.62/0.80  cnf(c_0_91, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])]), ['proof']).
% 0.62/0.80  # SZS output end CNFRefutation
% 0.62/0.80  # Proof object total steps             : 92
% 0.62/0.80  # Proof object clause steps            : 59
% 0.62/0.80  # Proof object formula steps           : 33
% 0.62/0.80  # Proof object conjectures             : 31
% 0.62/0.80  # Proof object clause conjectures      : 28
% 0.62/0.80  # Proof object formula conjectures     : 3
% 0.62/0.80  # Proof object initial clauses used    : 23
% 0.62/0.80  # Proof object initial formulas used   : 16
% 0.62/0.80  # Proof object generating inferences   : 28
% 0.62/0.80  # Proof object simplifying inferences  : 29
% 0.62/0.80  # Training examples: 0 positive, 0 negative
% 0.62/0.80  # Parsed axioms                        : 17
% 0.62/0.80  # Removed by relevancy pruning/SinE    : 0
% 0.62/0.80  # Initial clauses                      : 30
% 0.62/0.80  # Removed in clause preprocessing      : 9
% 0.62/0.80  # Initial clauses in saturation        : 21
% 0.62/0.80  # Processed clauses                    : 1769
% 0.62/0.80  # ...of these trivial                  : 32
% 0.62/0.80  # ...subsumed                          : 1013
% 0.62/0.80  # ...remaining for further processing  : 724
% 0.62/0.80  # Other redundant clauses eliminated   : 38
% 0.62/0.80  # Clauses deleted for lack of memory   : 0
% 0.62/0.80  # Backward-subsumed                    : 21
% 0.62/0.80  # Backward-rewritten                   : 79
% 0.62/0.80  # Generated clauses                    : 39929
% 0.62/0.80  # ...of the previous two non-trivial   : 30842
% 0.62/0.80  # Contextual simplify-reflections      : 5
% 0.62/0.80  # Paramodulations                      : 39885
% 0.62/0.80  # Factorizations                       : 6
% 0.62/0.80  # Equation resolutions                 : 38
% 0.62/0.80  # Propositional unsat checks           : 0
% 0.62/0.80  #    Propositional check models        : 0
% 0.62/0.80  #    Propositional check unsatisfiable : 0
% 0.62/0.80  #    Propositional clauses             : 0
% 0.62/0.80  #    Propositional clauses after purity: 0
% 0.62/0.80  #    Propositional unsat core size     : 0
% 0.62/0.80  #    Propositional preprocessing time  : 0.000
% 0.62/0.80  #    Propositional encoding time       : 0.000
% 0.62/0.80  #    Propositional solver time         : 0.000
% 0.62/0.80  #    Success case prop preproc time    : 0.000
% 0.62/0.80  #    Success case prop encoding time   : 0.000
% 0.62/0.80  #    Success case prop solver time     : 0.000
% 0.62/0.80  # Current number of processed clauses  : 601
% 0.62/0.80  #    Positive orientable unit clauses  : 51
% 0.62/0.80  #    Positive unorientable unit clauses: 0
% 0.62/0.80  #    Negative unit clauses             : 3
% 0.62/0.80  #    Non-unit-clauses                  : 547
% 0.62/0.80  # Current number of unprocessed clauses: 28858
% 0.62/0.80  # ...number of literals in the above   : 144033
% 0.62/0.80  # Current number of archived formulas  : 0
% 0.62/0.80  # Current number of archived clauses   : 129
% 0.62/0.80  # Clause-clause subsumption calls (NU) : 39738
% 0.62/0.80  # Rec. Clause-clause subsumption calls : 33204
% 0.62/0.80  # Non-unit clause-clause subsumptions  : 1005
% 0.62/0.80  # Unit Clause-clause subsumption calls : 206
% 0.62/0.80  # Rewrite failures with RHS unbound    : 0
% 0.62/0.80  # BW rewrite match attempts            : 29
% 0.62/0.80  # BW rewrite match successes           : 11
% 0.62/0.80  # Condensation attempts                : 0
% 0.62/0.80  # Condensation successes               : 0
% 0.62/0.80  # Termbank termtop insertions          : 900442
% 0.62/0.80  
% 0.62/0.80  # -------------------------------------------------
% 0.62/0.80  # User time                : 0.454 s
% 0.62/0.80  # System time              : 0.015 s
% 0.62/0.80  # Total time               : 0.469 s
% 0.62/0.80  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
