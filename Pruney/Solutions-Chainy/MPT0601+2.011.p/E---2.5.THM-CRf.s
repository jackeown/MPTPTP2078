%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:14 EST 2020

% Result     : Theorem 0.70s
% Output     : CNFRefutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 264 expanded)
%              Number of clauses        :   37 ( 105 expanded)
%              Number of leaves         :   17 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :  160 ( 478 expanded)
%              Number of equality atoms :   67 ( 258 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t56_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(t152_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( X1 != k1_xboole_0
          & r1_tarski(X1,k1_relat_1(X2))
          & k9_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(c_0_17,plain,(
    ! [X42,X43] :
      ( ~ v1_relat_1(X42)
      | k11_relat_1(X42,X43) = k9_relat_1(X42,k1_tarski(X43)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_18,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X15,X16,X17,X18] : k3_enumset1(X15,X15,X16,X17,X18) = k2_enumset1(X15,X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_22,plain,(
    ! [X19,X20,X21,X22,X23] : k4_enumset1(X19,X19,X20,X21,X22,X23) = k3_enumset1(X19,X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_23,plain,(
    ! [X24,X25,X26,X27,X28,X29] : k5_enumset1(X24,X24,X25,X26,X27,X28,X29) = k4_enumset1(X24,X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_24,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36] : k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36) = k5_enumset1(X30,X31,X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

cnf(c_0_26,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & ( ~ r2_hidden(esk9_0,k1_relat_1(esk10_0))
      | k11_relat_1(esk10_0,esk9_0) = k1_xboole_0 )
    & ( r2_hidden(esk9_0,k1_relat_1(esk10_0))
      | k11_relat_1(esk10_0,esk9_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_35,plain,(
    ! [X65,X66,X67] :
      ( ( ~ r2_hidden(k4_tarski(X65,X66),X67)
        | r2_hidden(X66,k11_relat_1(X67,X65))
        | ~ v1_relat_1(X67) )
      & ( ~ r2_hidden(X66,k11_relat_1(X67,X65))
        | r2_hidden(k4_tarski(X65,X66),X67)
        | ~ v1_relat_1(X67) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_36,plain,(
    ! [X37,X38,X39] :
      ( ( r2_hidden(X37,X39)
        | ~ r1_tarski(k2_tarski(X37,X38),X39) )
      & ( r2_hidden(X38,X39)
        | ~ r1_tarski(k2_tarski(X37,X38),X39) )
      & ( ~ r2_hidden(X37,X39)
        | ~ r2_hidden(X38,X39)
        | r1_tarski(k2_tarski(X37,X38),X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_37,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_39,plain,(
    ! [X52,X53,X54,X56,X57,X58,X59,X61] :
      ( ( ~ r2_hidden(X54,X53)
        | r2_hidden(k4_tarski(X54,esk4_3(X52,X53,X54)),X52)
        | X53 != k1_relat_1(X52) )
      & ( ~ r2_hidden(k4_tarski(X56,X57),X52)
        | r2_hidden(X56,X53)
        | X53 != k1_relat_1(X52) )
      & ( ~ r2_hidden(esk5_2(X58,X59),X59)
        | ~ r2_hidden(k4_tarski(esk5_2(X58,X59),X61),X58)
        | X59 = k1_relat_1(X58) )
      & ( r2_hidden(esk5_2(X58,X59),X59)
        | r2_hidden(k4_tarski(esk5_2(X58,X59),esk6_2(X58,X59)),X58)
        | X59 = k1_relat_1(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk9_0,k1_relat_1(esk10_0))
    | k11_relat_1(esk10_0,esk9_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k11_relat_1(esk10_0,X1) = k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_44,plain,(
    ! [X40,X41] : k2_xboole_0(k1_tarski(X40),X41) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk10_0)
    | ~ r2_hidden(X2,k11_relat_1(esk10_0,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_38])).

fof(c_0_47,plain,(
    ! [X68] :
      ( ~ v1_relat_1(X68)
      | r2_hidden(k4_tarski(esk7_1(X68),esk8_1(X68)),X68)
      | X68 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

fof(c_0_48,plain,(
    ! [X44,X45,X48,X50,X51] :
      ( ( ~ v1_relat_1(X44)
        | ~ r2_hidden(X45,X44)
        | X45 = k4_tarski(esk1_2(X44,X45),esk2_2(X44,X45)) )
      & ( r2_hidden(esk3_1(X48),X48)
        | v1_relat_1(X48) )
      & ( esk3_1(X48) != k4_tarski(X50,X51)
        | v1_relat_1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_49,plain,(
    ! [X63,X64] :
      ( ~ v1_relat_1(X64)
      | X63 = k1_xboole_0
      | ~ r1_tarski(X63,k1_relat_1(X64))
      | k9_relat_1(X64,X63) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_relat_1])])).

cnf(c_0_50,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk9_0,k1_relat_1(esk10_0))
    | k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_53,plain,(
    ! [X8] : k2_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk10_0)
    | ~ r2_hidden(X2,k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[c_0_46,c_0_43])).

cnf(c_0_56,plain,
    ( r2_hidden(k4_tarski(esk7_1(X1),esk8_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( X2 = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | k9_relat_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,esk9_0),k1_relat_1(esk10_0))
    | k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) != k1_xboole_0
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,plain,
    ( k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( k11_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | ~ r2_hidden(esk9_0,k1_relat_1(esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk10_0))
    | ~ r2_hidden(X2,k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(esk7_1(X1),esk8_1(X1)),X1)
    | r2_hidden(esk3_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( X1 = k1_xboole_0
    | k9_relat_1(esk10_0,X1) != k1_xboole_0
    | ~ r1_tarski(X1,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_38])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),k1_relat_1(esk10_0))
    | k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_51])).

cnf(c_0_67,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) = k1_xboole_0
    | ~ r2_hidden(esk9_0,k1_relat_1(esk10_0)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_43])).

cnf(c_0_69,negated_conjecture,
    ( k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:51:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.70/0.90  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.70/0.90  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.70/0.90  #
% 0.70/0.90  # Preprocessing time       : 0.028 s
% 0.70/0.90  # Presaturation interreduction done
% 0.70/0.90  
% 0.70/0.90  # Proof found!
% 0.70/0.90  # SZS status Theorem
% 0.70/0.90  # SZS output start CNFRefutation
% 0.70/0.90  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.70/0.90  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.70/0.90  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.70/0.90  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.70/0.90  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.70/0.90  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.70/0.90  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.70/0.90  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.70/0.90  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.70/0.90  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.70/0.90  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.70/0.90  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.70/0.90  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.70/0.90  fof(t56_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 0.70/0.90  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.70/0.90  fof(t152_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k1_relat_1(X2)))&k9_relat_1(X2,X1)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 0.70/0.90  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.70/0.90  fof(c_0_17, plain, ![X42, X43]:(~v1_relat_1(X42)|k11_relat_1(X42,X43)=k9_relat_1(X42,k1_tarski(X43))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.70/0.90  fof(c_0_18, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.70/0.90  fof(c_0_19, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.70/0.90  fof(c_0_20, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.70/0.90  fof(c_0_21, plain, ![X15, X16, X17, X18]:k3_enumset1(X15,X15,X16,X17,X18)=k2_enumset1(X15,X16,X17,X18), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.70/0.90  fof(c_0_22, plain, ![X19, X20, X21, X22, X23]:k4_enumset1(X19,X19,X20,X21,X22,X23)=k3_enumset1(X19,X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.70/0.90  fof(c_0_23, plain, ![X24, X25, X26, X27, X28, X29]:k5_enumset1(X24,X24,X25,X26,X27,X28,X29)=k4_enumset1(X24,X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.70/0.90  fof(c_0_24, plain, ![X30, X31, X32, X33, X34, X35, X36]:k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36)=k5_enumset1(X30,X31,X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.70/0.90  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.70/0.90  cnf(c_0_26, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.70/0.90  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.70/0.90  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.70/0.90  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.70/0.90  cnf(c_0_30, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.70/0.90  cnf(c_0_31, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.70/0.90  cnf(c_0_32, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.70/0.90  cnf(c_0_33, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.90  fof(c_0_34, negated_conjecture, (v1_relat_1(esk10_0)&((~r2_hidden(esk9_0,k1_relat_1(esk10_0))|k11_relat_1(esk10_0,esk9_0)=k1_xboole_0)&(r2_hidden(esk9_0,k1_relat_1(esk10_0))|k11_relat_1(esk10_0,esk9_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.70/0.90  fof(c_0_35, plain, ![X65, X66, X67]:((~r2_hidden(k4_tarski(X65,X66),X67)|r2_hidden(X66,k11_relat_1(X67,X65))|~v1_relat_1(X67))&(~r2_hidden(X66,k11_relat_1(X67,X65))|r2_hidden(k4_tarski(X65,X66),X67)|~v1_relat_1(X67))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.70/0.90  fof(c_0_36, plain, ![X37, X38, X39]:(((r2_hidden(X37,X39)|~r1_tarski(k2_tarski(X37,X38),X39))&(r2_hidden(X38,X39)|~r1_tarski(k2_tarski(X37,X38),X39)))&(~r2_hidden(X37,X39)|~r2_hidden(X38,X39)|r1_tarski(k2_tarski(X37,X38),X39))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.70/0.90  cnf(c_0_37, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33])).
% 0.70/0.90  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.70/0.90  fof(c_0_39, plain, ![X52, X53, X54, X56, X57, X58, X59, X61]:(((~r2_hidden(X54,X53)|r2_hidden(k4_tarski(X54,esk4_3(X52,X53,X54)),X52)|X53!=k1_relat_1(X52))&(~r2_hidden(k4_tarski(X56,X57),X52)|r2_hidden(X56,X53)|X53!=k1_relat_1(X52)))&((~r2_hidden(esk5_2(X58,X59),X59)|~r2_hidden(k4_tarski(esk5_2(X58,X59),X61),X58)|X59=k1_relat_1(X58))&(r2_hidden(esk5_2(X58,X59),X59)|r2_hidden(k4_tarski(esk5_2(X58,X59),esk6_2(X58,X59)),X58)|X59=k1_relat_1(X58)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.70/0.90  cnf(c_0_40, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.70/0.90  cnf(c_0_41, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.70/0.90  cnf(c_0_42, negated_conjecture, (r2_hidden(esk9_0,k1_relat_1(esk10_0))|k11_relat_1(esk10_0,esk9_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.70/0.90  cnf(c_0_43, negated_conjecture, (k11_relat_1(esk10_0,X1)=k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.70/0.90  fof(c_0_44, plain, ![X40, X41]:k2_xboole_0(k1_tarski(X40),X41)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.70/0.90  cnf(c_0_45, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.70/0.90  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk10_0)|~r2_hidden(X2,k11_relat_1(esk10_0,X1))), inference(spm,[status(thm)],[c_0_40, c_0_38])).
% 0.70/0.90  fof(c_0_47, plain, ![X68]:(~v1_relat_1(X68)|(r2_hidden(k4_tarski(esk7_1(X68),esk8_1(X68)),X68)|X68=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).
% 0.70/0.90  fof(c_0_48, plain, ![X44, X45, X48, X50, X51]:((~v1_relat_1(X44)|(~r2_hidden(X45,X44)|X45=k4_tarski(esk1_2(X44,X45),esk2_2(X44,X45))))&((r2_hidden(esk3_1(X48),X48)|v1_relat_1(X48))&(esk3_1(X48)!=k4_tarski(X50,X51)|v1_relat_1(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.70/0.90  fof(c_0_49, plain, ![X63, X64]:(~v1_relat_1(X64)|(X63=k1_xboole_0|~r1_tarski(X63,k1_relat_1(X64))|k9_relat_1(X64,X63)!=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_relat_1])])).
% 0.70/0.90  cnf(c_0_50, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33])).
% 0.70/0.90  cnf(c_0_51, negated_conjecture, (r2_hidden(esk9_0,k1_relat_1(esk10_0))|k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.70/0.90  cnf(c_0_52, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.70/0.90  fof(c_0_53, plain, ![X8]:k2_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.70/0.90  cnf(c_0_54, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_45])).
% 0.70/0.90  cnf(c_0_55, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk10_0)|~r2_hidden(X2,k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))), inference(rw,[status(thm)],[c_0_46, c_0_43])).
% 0.70/0.90  cnf(c_0_56, plain, (r2_hidden(k4_tarski(esk7_1(X1),esk8_1(X1)),X1)|X1=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.70/0.90  cnf(c_0_57, plain, (r2_hidden(esk3_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.70/0.90  cnf(c_0_58, plain, (X2=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|k9_relat_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.70/0.90  cnf(c_0_59, negated_conjecture, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,esk9_0),k1_relat_1(esk10_0))|k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))!=k1_xboole_0|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.70/0.90  cnf(c_0_60, plain, (k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33])).
% 0.70/0.90  cnf(c_0_61, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.70/0.90  cnf(c_0_62, negated_conjecture, (k11_relat_1(esk10_0,esk9_0)=k1_xboole_0|~r2_hidden(esk9_0,k1_relat_1(esk10_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.70/0.90  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk10_0))|~r2_hidden(X2,k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.70/0.90  cnf(c_0_64, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(esk7_1(X1),esk8_1(X1)),X1)|r2_hidden(esk3_1(X1),X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.70/0.90  cnf(c_0_65, negated_conjecture, (X1=k1_xboole_0|k9_relat_1(esk10_0,X1)!=k1_xboole_0|~r1_tarski(X1,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_58, c_0_38])).
% 0.70/0.90  cnf(c_0_66, negated_conjecture, (r1_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),k1_relat_1(esk10_0))|k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_51])).
% 0.70/0.90  cnf(c_0_67, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.70/0.90  cnf(c_0_68, negated_conjecture, (k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))=k1_xboole_0|~r2_hidden(esk9_0,k1_relat_1(esk10_0))), inference(rw,[status(thm)],[c_0_62, c_0_43])).
% 0.70/0.90  cnf(c_0_69, negated_conjecture, (k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk10_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_63])).
% 0.70/0.90  cnf(c_0_70, negated_conjecture, (k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 0.70/0.90  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), ['proof']).
% 0.70/0.90  # SZS output end CNFRefutation
% 0.70/0.90  # Proof object total steps             : 72
% 0.70/0.90  # Proof object clause steps            : 37
% 0.70/0.90  # Proof object formula steps           : 35
% 0.70/0.90  # Proof object conjectures             : 18
% 0.70/0.90  # Proof object clause conjectures      : 15
% 0.70/0.90  # Proof object formula conjectures     : 3
% 0.70/0.90  # Proof object initial clauses used    : 19
% 0.70/0.90  # Proof object initial formulas used   : 17
% 0.70/0.90  # Proof object generating inferences   : 11
% 0.70/0.90  # Proof object simplifying inferences  : 27
% 0.70/0.90  # Training examples: 0 positive, 0 negative
% 0.70/0.90  # Parsed axioms                        : 17
% 0.70/0.90  # Removed by relevancy pruning/SinE    : 0
% 0.70/0.90  # Initial clauses                      : 27
% 0.70/0.90  # Removed in clause preprocessing      : 7
% 0.70/0.90  # Initial clauses in saturation        : 20
% 0.70/0.90  # Processed clauses                    : 1440
% 0.70/0.90  # ...of these trivial                  : 69
% 0.70/0.90  # ...subsumed                          : 515
% 0.70/0.90  # ...remaining for further processing  : 856
% 0.70/0.90  # Other redundant clauses eliminated   : 2
% 0.70/0.90  # Clauses deleted for lack of memory   : 0
% 0.70/0.90  # Backward-subsumed                    : 20
% 0.70/0.90  # Backward-rewritten                   : 268
% 0.70/0.90  # Generated clauses                    : 38692
% 0.70/0.90  # ...of the previous two non-trivial   : 37853
% 0.70/0.90  # Contextual simplify-reflections      : 27
% 0.70/0.90  # Paramodulations                      : 38495
% 0.70/0.90  # Factorizations                       : 110
% 0.70/0.90  # Equation resolutions                 : 9
% 0.70/0.90  # Propositional unsat checks           : 0
% 0.70/0.90  #    Propositional check models        : 0
% 0.70/0.90  #    Propositional check unsatisfiable : 0
% 0.70/0.90  #    Propositional clauses             : 0
% 0.70/0.90  #    Propositional clauses after purity: 0
% 0.70/0.90  #    Propositional unsat core size     : 0
% 0.70/0.90  #    Propositional preprocessing time  : 0.000
% 0.70/0.90  #    Propositional encoding time       : 0.000
% 0.70/0.90  #    Propositional solver time         : 0.000
% 0.70/0.90  #    Success case prop preproc time    : 0.000
% 0.70/0.90  #    Success case prop encoding time   : 0.000
% 0.70/0.90  #    Success case prop solver time     : 0.000
% 0.70/0.90  # Current number of processed clauses  : 520
% 0.70/0.90  #    Positive orientable unit clauses  : 12
% 0.70/0.90  #    Positive unorientable unit clauses: 0
% 0.70/0.90  #    Negative unit clauses             : 10
% 0.70/0.90  #    Non-unit-clauses                  : 498
% 0.70/0.90  # Current number of unprocessed clauses: 36074
% 0.70/0.90  # ...number of literals in the above   : 158764
% 0.70/0.90  # Current number of archived formulas  : 0
% 0.70/0.90  # Current number of archived clauses   : 315
% 0.70/0.90  # Clause-clause subsumption calls (NU) : 31375
% 0.70/0.90  # Rec. Clause-clause subsumption calls : 11214
% 0.70/0.90  # Non-unit clause-clause subsumptions  : 494
% 0.70/0.90  # Unit Clause-clause subsumption calls : 853
% 0.70/0.90  # Rewrite failures with RHS unbound    : 0
% 0.70/0.90  # BW rewrite match attempts            : 48
% 0.70/0.90  # BW rewrite match successes           : 35
% 0.70/0.90  # Condensation attempts                : 0
% 0.70/0.90  # Condensation successes               : 0
% 0.70/0.90  # Termbank termtop insertions          : 1375893
% 0.70/0.90  
% 0.70/0.90  # -------------------------------------------------
% 0.70/0.90  # User time                : 0.527 s
% 0.70/0.90  # System time              : 0.033 s
% 0.70/0.90  # Total time               : 0.560 s
% 0.70/0.90  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
