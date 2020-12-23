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
% DateTime   : Thu Dec  3 10:52:13 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 231 expanded)
%              Number of clauses        :   36 (  92 expanded)
%              Number of leaves         :   17 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :  151 ( 415 expanded)
%              Number of equality atoms :   66 ( 224 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

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

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

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

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

fof(c_0_18,plain,(
    ! [X41,X42] :
      ( ~ v1_relat_1(X41)
      | k11_relat_1(X41,X42) = k9_relat_1(X41,k1_tarski(X42)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_19,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X15,X16,X17,X18] : k3_enumset1(X15,X15,X16,X17,X18) = k2_enumset1(X15,X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,plain,(
    ! [X19,X20,X21,X22,X23] : k4_enumset1(X19,X19,X20,X21,X22,X23) = k3_enumset1(X19,X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_24,plain,(
    ! [X24,X25,X26,X27,X28,X29] : k5_enumset1(X24,X24,X25,X26,X27,X28,X29) = k4_enumset1(X24,X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_25,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36] : k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36) = k5_enumset1(X30,X31,X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_26,plain,(
    ! [X64,X65,X66] :
      ( ( ~ r2_hidden(k4_tarski(X64,X65),X66)
        | r2_hidden(X65,k11_relat_1(X66,X64))
        | ~ v1_relat_1(X66) )
      & ( ~ r2_hidden(X65,k11_relat_1(X66,X64))
        | r2_hidden(k4_tarski(X64,X65),X66)
        | ~ v1_relat_1(X66) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_27,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & ( ~ r2_hidden(esk9_0,k1_relat_1(esk10_0))
      | k11_relat_1(esk10_0,esk9_0) = k1_xboole_0 )
    & ( r2_hidden(esk9_0,k1_relat_1(esk10_0))
      | k11_relat_1(esk10_0,esk9_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_28,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_36,plain,(
    ! [X51,X52,X53,X55,X56,X57,X58,X60] :
      ( ( ~ r2_hidden(X53,X52)
        | r2_hidden(k4_tarski(X53,esk4_3(X51,X52,X53)),X51)
        | X52 != k1_relat_1(X51) )
      & ( ~ r2_hidden(k4_tarski(X55,X56),X51)
        | r2_hidden(X55,X52)
        | X52 != k1_relat_1(X51) )
      & ( ~ r2_hidden(esk5_2(X57,X58),X58)
        | ~ r2_hidden(k4_tarski(esk5_2(X57,X58),X60),X57)
        | X58 = k1_relat_1(X57) )
      & ( r2_hidden(esk5_2(X57,X58),X58)
        | r2_hidden(k4_tarski(esk5_2(X57,X58),esk6_2(X57,X58)),X57)
        | X58 = k1_relat_1(X57) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

fof(c_0_40,plain,(
    ! [X37,X38] :
      ( ( ~ r1_tarski(k1_tarski(X37),X38)
        | r2_hidden(X37,X38) )
      & ( ~ r2_hidden(X37,X38)
        | r1_tarski(k1_tarski(X37),X38) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_41,plain,(
    ! [X39,X40] : k2_xboole_0(k1_tarski(X39),X40) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk10_0)
    | ~ r2_hidden(X2,k11_relat_1(esk10_0,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k11_relat_1(esk10_0,X1) = k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

fof(c_0_45,plain,(
    ! [X67] :
      ( ~ v1_relat_1(X67)
      | r2_hidden(k4_tarski(esk7_1(X67),esk8_1(X67)),X67)
      | X67 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

fof(c_0_46,plain,(
    ! [X43,X44,X47,X49,X50] :
      ( ( ~ v1_relat_1(X43)
        | ~ r2_hidden(X44,X43)
        | X44 = k4_tarski(esk1_2(X43,X44),esk2_2(X43,X44)) )
      & ( r2_hidden(esk3_1(X47),X47)
        | v1_relat_1(X47) )
      & ( esk3_1(X47) != k4_tarski(X49,X50)
        | v1_relat_1(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_47,plain,(
    ! [X62,X63] :
      ( ~ v1_relat_1(X63)
      | X62 = k1_xboole_0
      | ~ r1_tarski(X62,k1_relat_1(X63))
      | k9_relat_1(X63,X62) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_relat_1])])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk9_0,k1_relat_1(esk10_0))
    | k11_relat_1(esk10_0,esk9_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_50,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_51,plain,(
    ! [X8] : k2_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk10_0)
    | ~ r2_hidden(X2,k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,plain,
    ( r2_hidden(k4_tarski(esk7_1(X1),esk8_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( X2 = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | k9_relat_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk9_0,k1_relat_1(esk10_0))
    | k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_44])).

cnf(c_0_59,plain,
    ( k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( k11_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | ~ r2_hidden(esk9_0,k1_relat_1(esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk10_0))
    | ~ r2_hidden(X2,k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(esk7_1(X1),esk8_1(X1)),X1)
    | r2_hidden(esk3_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( X1 = k1_xboole_0
    | k9_relat_1(esk10_0,X1) != k1_xboole_0
    | ~ r1_tarski(X1,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_38])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),k1_relat_1(esk10_0))
    | k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) = k1_xboole_0
    | ~ r2_hidden(esk9_0,k1_relat_1(esk10_0)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_44])).

cnf(c_0_68,negated_conjecture,
    ( k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:42:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.64  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.47/0.64  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.47/0.64  #
% 0.47/0.64  # Preprocessing time       : 0.027 s
% 0.47/0.64  # Presaturation interreduction done
% 0.47/0.64  
% 0.47/0.64  # Proof found!
% 0.47/0.64  # SZS status Theorem
% 0.47/0.64  # SZS output start CNFRefutation
% 0.47/0.64  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.47/0.64  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.47/0.64  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.47/0.64  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.47/0.64  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.47/0.64  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.47/0.64  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.47/0.64  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.47/0.64  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.47/0.64  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.47/0.64  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.47/0.64  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.47/0.64  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.47/0.64  fof(t56_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 0.47/0.64  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.47/0.64  fof(t152_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k1_relat_1(X2)))&k9_relat_1(X2,X1)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 0.47/0.64  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.47/0.64  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.47/0.64  fof(c_0_18, plain, ![X41, X42]:(~v1_relat_1(X41)|k11_relat_1(X41,X42)=k9_relat_1(X41,k1_tarski(X42))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.47/0.64  fof(c_0_19, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.47/0.64  fof(c_0_20, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.47/0.64  fof(c_0_21, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.47/0.64  fof(c_0_22, plain, ![X15, X16, X17, X18]:k3_enumset1(X15,X15,X16,X17,X18)=k2_enumset1(X15,X16,X17,X18), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.47/0.64  fof(c_0_23, plain, ![X19, X20, X21, X22, X23]:k4_enumset1(X19,X19,X20,X21,X22,X23)=k3_enumset1(X19,X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.47/0.64  fof(c_0_24, plain, ![X24, X25, X26, X27, X28, X29]:k5_enumset1(X24,X24,X25,X26,X27,X28,X29)=k4_enumset1(X24,X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.47/0.64  fof(c_0_25, plain, ![X30, X31, X32, X33, X34, X35, X36]:k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36)=k5_enumset1(X30,X31,X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.47/0.64  fof(c_0_26, plain, ![X64, X65, X66]:((~r2_hidden(k4_tarski(X64,X65),X66)|r2_hidden(X65,k11_relat_1(X66,X64))|~v1_relat_1(X66))&(~r2_hidden(X65,k11_relat_1(X66,X64))|r2_hidden(k4_tarski(X64,X65),X66)|~v1_relat_1(X66))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.47/0.64  fof(c_0_27, negated_conjecture, (v1_relat_1(esk10_0)&((~r2_hidden(esk9_0,k1_relat_1(esk10_0))|k11_relat_1(esk10_0,esk9_0)=k1_xboole_0)&(r2_hidden(esk9_0,k1_relat_1(esk10_0))|k11_relat_1(esk10_0,esk9_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.47/0.64  cnf(c_0_28, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.64  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.64  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.64  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.64  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.47/0.64  cnf(c_0_33, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.47/0.64  cnf(c_0_34, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.64  cnf(c_0_35, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.47/0.64  fof(c_0_36, plain, ![X51, X52, X53, X55, X56, X57, X58, X60]:(((~r2_hidden(X53,X52)|r2_hidden(k4_tarski(X53,esk4_3(X51,X52,X53)),X51)|X52!=k1_relat_1(X51))&(~r2_hidden(k4_tarski(X55,X56),X51)|r2_hidden(X55,X52)|X52!=k1_relat_1(X51)))&((~r2_hidden(esk5_2(X57,X58),X58)|~r2_hidden(k4_tarski(esk5_2(X57,X58),X60),X57)|X58=k1_relat_1(X57))&(r2_hidden(esk5_2(X57,X58),X58)|r2_hidden(k4_tarski(esk5_2(X57,X58),esk6_2(X57,X58)),X57)|X58=k1_relat_1(X57)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.47/0.64  cnf(c_0_37, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.64  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.47/0.64  cnf(c_0_39, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.47/0.64  fof(c_0_40, plain, ![X37, X38]:((~r1_tarski(k1_tarski(X37),X38)|r2_hidden(X37,X38))&(~r2_hidden(X37,X38)|r1_tarski(k1_tarski(X37),X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.47/0.64  fof(c_0_41, plain, ![X39, X40]:k2_xboole_0(k1_tarski(X39),X40)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.47/0.64  cnf(c_0_42, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.47/0.64  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk10_0)|~r2_hidden(X2,k11_relat_1(esk10_0,X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.47/0.64  cnf(c_0_44, negated_conjecture, (k11_relat_1(esk10_0,X1)=k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 0.47/0.64  fof(c_0_45, plain, ![X67]:(~v1_relat_1(X67)|(r2_hidden(k4_tarski(esk7_1(X67),esk8_1(X67)),X67)|X67=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).
% 0.47/0.64  fof(c_0_46, plain, ![X43, X44, X47, X49, X50]:((~v1_relat_1(X43)|(~r2_hidden(X44,X43)|X44=k4_tarski(esk1_2(X43,X44),esk2_2(X43,X44))))&((r2_hidden(esk3_1(X47),X47)|v1_relat_1(X47))&(esk3_1(X47)!=k4_tarski(X49,X50)|v1_relat_1(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.47/0.64  fof(c_0_47, plain, ![X62, X63]:(~v1_relat_1(X63)|(X62=k1_xboole_0|~r1_tarski(X62,k1_relat_1(X63))|k9_relat_1(X63,X62)!=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_relat_1])])).
% 0.47/0.64  cnf(c_0_48, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.47/0.64  cnf(c_0_49, negated_conjecture, (r2_hidden(esk9_0,k1_relat_1(esk10_0))|k11_relat_1(esk10_0,esk9_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.47/0.64  cnf(c_0_50, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.47/0.64  fof(c_0_51, plain, ![X8]:k2_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.47/0.64  cnf(c_0_52, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_42])).
% 0.47/0.64  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk10_0)|~r2_hidden(X2,k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.47/0.64  cnf(c_0_54, plain, (r2_hidden(k4_tarski(esk7_1(X1),esk8_1(X1)),X1)|X1=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.47/0.64  cnf(c_0_55, plain, (r2_hidden(esk3_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.47/0.64  cnf(c_0_56, plain, (X2=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|k9_relat_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.47/0.64  cnf(c_0_57, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.47/0.64  cnf(c_0_58, negated_conjecture, (r2_hidden(esk9_0,k1_relat_1(esk10_0))|k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_49, c_0_44])).
% 0.47/0.64  cnf(c_0_59, plain, (k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.47/0.64  cnf(c_0_60, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.47/0.64  cnf(c_0_61, negated_conjecture, (k11_relat_1(esk10_0,esk9_0)=k1_xboole_0|~r2_hidden(esk9_0,k1_relat_1(esk10_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.47/0.64  cnf(c_0_62, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk10_0))|~r2_hidden(X2,k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.47/0.64  cnf(c_0_63, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(esk7_1(X1),esk8_1(X1)),X1)|r2_hidden(esk3_1(X1),X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.47/0.64  cnf(c_0_64, negated_conjecture, (X1=k1_xboole_0|k9_relat_1(esk10_0,X1)!=k1_xboole_0|~r1_tarski(X1,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_56, c_0_38])).
% 0.47/0.64  cnf(c_0_65, negated_conjecture, (r1_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),k1_relat_1(esk10_0))|k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.47/0.64  cnf(c_0_66, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.47/0.64  cnf(c_0_67, negated_conjecture, (k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))=k1_xboole_0|~r2_hidden(esk9_0,k1_relat_1(esk10_0))), inference(rw,[status(thm)],[c_0_61, c_0_44])).
% 0.47/0.64  cnf(c_0_68, negated_conjecture, (k9_relat_1(esk10_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk10_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_62])).
% 0.47/0.64  cnf(c_0_69, negated_conjecture, (k9_relat_1(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.47/0.64  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), ['proof']).
% 0.47/0.64  # SZS output end CNFRefutation
% 0.47/0.64  # Proof object total steps             : 71
% 0.47/0.64  # Proof object clause steps            : 36
% 0.47/0.64  # Proof object formula steps           : 35
% 0.47/0.64  # Proof object conjectures             : 17
% 0.47/0.64  # Proof object clause conjectures      : 14
% 0.47/0.64  # Proof object formula conjectures     : 3
% 0.47/0.64  # Proof object initial clauses used    : 19
% 0.47/0.64  # Proof object initial formulas used   : 17
% 0.47/0.64  # Proof object generating inferences   : 10
% 0.47/0.64  # Proof object simplifying inferences  : 28
% 0.47/0.64  # Training examples: 0 positive, 0 negative
% 0.47/0.64  # Parsed axioms                        : 17
% 0.47/0.64  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.64  # Initial clauses                      : 26
% 0.47/0.64  # Removed in clause preprocessing      : 7
% 0.47/0.64  # Initial clauses in saturation        : 19
% 0.47/0.64  # Processed clauses                    : 1026
% 0.47/0.64  # ...of these trivial                  : 9
% 0.47/0.64  # ...subsumed                          : 410
% 0.47/0.64  # ...remaining for further processing  : 607
% 0.47/0.64  # Other redundant clauses eliminated   : 2
% 0.47/0.64  # Clauses deleted for lack of memory   : 0
% 0.47/0.64  # Backward-subsumed                    : 23
% 0.47/0.64  # Backward-rewritten                   : 17
% 0.47/0.64  # Generated clauses                    : 16939
% 0.47/0.64  # ...of the previous two non-trivial   : 16621
% 0.47/0.64  # Contextual simplify-reflections      : 20
% 0.47/0.64  # Paramodulations                      : 16825
% 0.47/0.64  # Factorizations                       : 108
% 0.47/0.64  # Equation resolutions                 : 6
% 0.47/0.64  # Propositional unsat checks           : 0
% 0.47/0.64  #    Propositional check models        : 0
% 0.47/0.64  #    Propositional check unsatisfiable : 0
% 0.47/0.64  #    Propositional clauses             : 0
% 0.47/0.64  #    Propositional clauses after purity: 0
% 0.47/0.64  #    Propositional unsat core size     : 0
% 0.47/0.64  #    Propositional preprocessing time  : 0.000
% 0.47/0.64  #    Propositional encoding time       : 0.000
% 0.47/0.64  #    Propositional solver time         : 0.000
% 0.47/0.64  #    Success case prop preproc time    : 0.000
% 0.47/0.64  #    Success case prop encoding time   : 0.000
% 0.47/0.64  #    Success case prop solver time     : 0.000
% 0.47/0.64  # Current number of processed clauses  : 546
% 0.47/0.64  #    Positive orientable unit clauses  : 9
% 0.47/0.64  #    Positive unorientable unit clauses: 0
% 0.47/0.64  #    Negative unit clauses             : 12
% 0.47/0.64  #    Non-unit-clauses                  : 525
% 0.47/0.64  # Current number of unprocessed clauses: 15487
% 0.47/0.64  # ...number of literals in the above   : 63671
% 0.47/0.64  # Current number of archived formulas  : 0
% 0.47/0.64  # Current number of archived clauses   : 66
% 0.47/0.64  # Clause-clause subsumption calls (NU) : 23513
% 0.47/0.64  # Rec. Clause-clause subsumption calls : 5098
% 0.47/0.64  # Non-unit clause-clause subsumptions  : 432
% 0.47/0.64  # Unit Clause-clause subsumption calls : 129
% 0.47/0.64  # Rewrite failures with RHS unbound    : 0
% 0.47/0.64  # BW rewrite match attempts            : 22
% 0.47/0.64  # BW rewrite match successes           : 9
% 0.47/0.64  # Condensation attempts                : 0
% 0.47/0.64  # Condensation successes               : 0
% 0.47/0.64  # Termbank termtop insertions          : 693436
% 0.47/0.64  
% 0.47/0.64  # -------------------------------------------------
% 0.47/0.64  # User time                : 0.293 s
% 0.47/0.64  # System time              : 0.012 s
% 0.47/0.64  # Total time               : 0.305 s
% 0.47/0.64  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
