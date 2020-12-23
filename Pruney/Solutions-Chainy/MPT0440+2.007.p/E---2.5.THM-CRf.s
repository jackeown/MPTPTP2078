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
% DateTime   : Thu Dec  3 10:48:12 EST 2020

% Result     : Theorem 1.02s
% Output     : CNFRefutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   77 (2168 expanded)
%              Number of clauses        :   48 ( 813 expanded)
%              Number of leaves         :   14 ( 667 expanded)
%              Depth                    :   14
%              Number of atoms          :  172 (3034 expanded)
%              Number of equality atoms :   73 (2294 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( X3 = k1_tarski(k4_tarski(X1,X2))
       => ( k1_relat_1(X3) = k1_tarski(X1)
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

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

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( X3 = k1_tarski(k4_tarski(X1,X2))
         => ( k1_relat_1(X3) = k1_tarski(X1)
            & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_relat_1])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & esk10_0 = k1_tarski(k4_tarski(esk8_0,esk9_0))
    & ( k1_relat_1(esk10_0) != k1_tarski(esk8_0)
      | k2_relat_1(esk10_0) != k1_tarski(esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_16,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,plain,(
    ! [X25,X26,X27,X28,X29] : k4_enumset1(X25,X25,X26,X27,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_21,plain,(
    ! [X30,X31,X32,X33,X34,X35] : k5_enumset1(X30,X30,X31,X32,X33,X34,X35) = k4_enumset1(X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_22,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42] : k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42) = k5_enumset1(X36,X37,X38,X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_23,plain,(
    ! [X47,X48,X49] :
      ( k2_zfmisc_1(k1_tarski(X47),k2_tarski(X48,X49)) = k2_tarski(k4_tarski(X47,X48),k4_tarski(X47,X49))
      & k2_zfmisc_1(k2_tarski(X47,X48),k1_tarski(X49)) = k2_tarski(k4_tarski(X47,X49),k4_tarski(X48,X49)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_24,negated_conjecture,
    ( esk10_0 = k1_tarski(k4_tarski(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X50,X51,X52] :
      ( ( r2_hidden(X50,X52)
        | ~ r1_tarski(k2_tarski(X50,X51),X52) )
      & ( r2_hidden(X51,X52)
        | ~ r1_tarski(k2_tarski(X50,X51),X52) )
      & ( ~ r2_hidden(X50,X52)
        | ~ r2_hidden(X51,X52)
        | r1_tarski(k2_tarski(X50,X51),X52) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_34,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_35,plain,(
    ! [X43,X44,X45,X46] :
      ( ( r2_hidden(X43,X45)
        | ~ r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(X45,X46)) )
      & ( r2_hidden(X44,X46)
        | ~ r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(X45,X46)) )
      & ( ~ r2_hidden(X43,X45)
        | ~ r2_hidden(X44,X46)
        | r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(X45,X46)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_36,negated_conjecture,
    ( esk10_0 = k6_enumset1(k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) = k6_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k2_zfmisc_1(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) = esk10_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_42,plain,(
    ! [X53,X54,X55,X57,X58,X59,X60,X62] :
      ( ( ~ r2_hidden(X55,X54)
        | r2_hidden(k4_tarski(X55,esk2_3(X53,X54,X55)),X53)
        | X54 != k1_relat_1(X53) )
      & ( ~ r2_hidden(k4_tarski(X57,X58),X53)
        | r2_hidden(X57,X54)
        | X54 != k1_relat_1(X53) )
      & ( ~ r2_hidden(esk3_2(X59,X60),X60)
        | ~ r2_hidden(k4_tarski(esk3_2(X59,X60),X62),X59)
        | X60 = k1_relat_1(X59) )
      & ( r2_hidden(esk3_2(X59,X60),X60)
        | r2_hidden(k4_tarski(esk3_2(X59,X60),esk4_2(X59,X60)),X59)
        | X60 = k1_relat_1(X59) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))
    | ~ r2_hidden(k4_tarski(X1,X2),esk10_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( X1 = k1_relat_1(esk10_0)
    | r2_hidden(esk3_2(esk10_0,X1),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))
    | r2_hidden(esk3_2(esk10_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_50,plain,(
    ! [X64,X65,X66,X68,X69,X70,X71,X73] :
      ( ( ~ r2_hidden(X66,X65)
        | r2_hidden(k4_tarski(esk5_3(X64,X65,X66),X66),X64)
        | X65 != k2_relat_1(X64) )
      & ( ~ r2_hidden(k4_tarski(X69,X68),X64)
        | r2_hidden(X68,X65)
        | X65 != k2_relat_1(X64) )
      & ( ~ r2_hidden(esk6_2(X70,X71),X71)
        | ~ r2_hidden(k4_tarski(X73,esk6_2(X70,X71)),X70)
        | X71 = k2_relat_1(X70) )
      & ( r2_hidden(esk6_2(X70,X71),X71)
        | r2_hidden(k4_tarski(esk7_2(X70,X71),esk6_2(X70,X71)),X70)
        | X71 = k2_relat_1(X70) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_51,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) = k1_relat_1(esk10_0)
    | r2_hidden(esk3_2(esk10_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(ef,[status(thm)],[c_0_49])).

cnf(c_0_53,plain,
    ( X2 = k1_relat_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_55,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) = k1_relat_1(esk10_0)
    | r2_hidden(k4_tarski(esk3_2(esk10_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),X1),k2_zfmisc_1(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) = k1_relat_1(esk10_0)
    | ~ r2_hidden(k4_tarski(esk3_2(esk10_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),X1),esk10_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k1_relat_1(esk10_0) != k1_tarski(esk8_0)
    | k2_relat_1(esk10_0) != k1_tarski(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_59,plain,
    ( X1 = k2_relat_1(k2_zfmisc_1(X2,X3))
    | r2_hidden(esk6_2(k2_zfmisc_1(X2,X3),X1),X1)
    | r2_hidden(esk6_2(k2_zfmisc_1(X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) = k1_relat_1(esk10_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_41]),c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k1_relat_1(esk10_0) != k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)
    | k2_relat_1(esk10_0) != k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31])).

cnf(c_0_62,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(k2_zfmisc_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_37])).

cnf(c_0_63,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | r2_hidden(esk6_2(k2_zfmisc_1(X1,X2),X2),X2) ),
    inference(ef,[status(thm)],[c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k2_zfmisc_1(k1_relat_1(esk10_0),k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) = esk10_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0) != k2_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_60])])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk9_0),X1)
    | ~ r1_tarski(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_41])).

cnf(c_0_68,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk6_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk6_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk6_2(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk9_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_44])).

cnf(c_0_72,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | ~ r2_hidden(k4_tarski(X3,esk6_2(k2_zfmisc_1(X1,X2),X2)),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk6_2(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))),k2_zfmisc_1(X2,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk8_0,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk6_2(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))),esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_64]),c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_64]),c_0_75]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:54:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 1.02/1.19  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 1.02/1.19  # and selection function GSelectMinInfpos.
% 1.02/1.19  #
% 1.02/1.19  # Preprocessing time       : 0.033 s
% 1.02/1.19  # Presaturation interreduction done
% 1.02/1.19  
% 1.02/1.19  # Proof found!
% 1.02/1.19  # SZS status Theorem
% 1.02/1.19  # SZS output start CNFRefutation
% 1.02/1.19  fof(t23_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relat_1)).
% 1.02/1.19  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.02/1.19  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.02/1.19  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.02/1.19  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.02/1.19  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.02/1.19  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 1.02/1.19  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 1.02/1.19  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 1.02/1.19  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.02/1.19  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.02/1.19  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.02/1.19  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 1.02/1.19  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 1.02/1.19  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2))))), inference(assume_negation,[status(cth)],[t23_relat_1])).
% 1.02/1.19  fof(c_0_15, negated_conjecture, (v1_relat_1(esk10_0)&(esk10_0=k1_tarski(k4_tarski(esk8_0,esk9_0))&(k1_relat_1(esk10_0)!=k1_tarski(esk8_0)|k2_relat_1(esk10_0)!=k1_tarski(esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 1.02/1.19  fof(c_0_16, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.02/1.19  fof(c_0_17, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.02/1.19  fof(c_0_18, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.02/1.19  fof(c_0_19, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.02/1.19  fof(c_0_20, plain, ![X25, X26, X27, X28, X29]:k4_enumset1(X25,X25,X26,X27,X28,X29)=k3_enumset1(X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 1.02/1.19  fof(c_0_21, plain, ![X30, X31, X32, X33, X34, X35]:k5_enumset1(X30,X30,X31,X32,X33,X34,X35)=k4_enumset1(X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 1.02/1.19  fof(c_0_22, plain, ![X36, X37, X38, X39, X40, X41, X42]:k6_enumset1(X36,X36,X37,X38,X39,X40,X41,X42)=k5_enumset1(X36,X37,X38,X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 1.02/1.19  fof(c_0_23, plain, ![X47, X48, X49]:(k2_zfmisc_1(k1_tarski(X47),k2_tarski(X48,X49))=k2_tarski(k4_tarski(X47,X48),k4_tarski(X47,X49))&k2_zfmisc_1(k2_tarski(X47,X48),k1_tarski(X49))=k2_tarski(k4_tarski(X47,X49),k4_tarski(X48,X49))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 1.02/1.19  cnf(c_0_24, negated_conjecture, (esk10_0=k1_tarski(k4_tarski(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.02/1.19  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.02/1.19  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.02/1.19  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.02/1.19  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.02/1.19  cnf(c_0_29, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.02/1.19  cnf(c_0_30, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.02/1.19  cnf(c_0_31, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.02/1.19  cnf(c_0_32, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.02/1.19  fof(c_0_33, plain, ![X50, X51, X52]:(((r2_hidden(X50,X52)|~r1_tarski(k2_tarski(X50,X51),X52))&(r2_hidden(X51,X52)|~r1_tarski(k2_tarski(X50,X51),X52)))&(~r2_hidden(X50,X52)|~r2_hidden(X51,X52)|r1_tarski(k2_tarski(X50,X51),X52))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 1.02/1.19  fof(c_0_34, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.02/1.19  fof(c_0_35, plain, ![X43, X44, X45, X46]:(((r2_hidden(X43,X45)|~r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(X45,X46)))&(r2_hidden(X44,X46)|~r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(X45,X46))))&(~r2_hidden(X43,X45)|~r2_hidden(X44,X46)|r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(X45,X46)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 1.02/1.19  cnf(c_0_36, negated_conjecture, (esk10_0=k6_enumset1(k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0),k4_tarski(esk8_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 1.02/1.19  cnf(c_0_37, plain, (k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))=k6_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_31])).
% 1.02/1.19  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.02/1.19  cnf(c_0_39, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.02/1.19  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.02/1.19  cnf(c_0_41, negated_conjecture, (k2_zfmisc_1(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))=esk10_0), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 1.02/1.19  fof(c_0_42, plain, ![X53, X54, X55, X57, X58, X59, X60, X62]:(((~r2_hidden(X55,X54)|r2_hidden(k4_tarski(X55,esk2_3(X53,X54,X55)),X53)|X54!=k1_relat_1(X53))&(~r2_hidden(k4_tarski(X57,X58),X53)|r2_hidden(X57,X54)|X54!=k1_relat_1(X53)))&((~r2_hidden(esk3_2(X59,X60),X60)|~r2_hidden(k4_tarski(esk3_2(X59,X60),X62),X59)|X60=k1_relat_1(X59))&(r2_hidden(esk3_2(X59,X60),X60)|r2_hidden(k4_tarski(esk3_2(X59,X60),esk4_2(X59,X60)),X59)|X60=k1_relat_1(X59)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 1.02/1.19  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r1_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 1.02/1.19  cnf(c_0_44, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_39])).
% 1.02/1.19  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))|~r2_hidden(k4_tarski(X1,X2),esk10_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.02/1.19  cnf(c_0_46, plain, (r2_hidden(esk3_2(X1,X2),X2)|r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.02/1.19  cnf(c_0_47, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.02/1.19  cnf(c_0_48, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 1.02/1.19  cnf(c_0_49, negated_conjecture, (X1=k1_relat_1(esk10_0)|r2_hidden(esk3_2(esk10_0,X1),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))|r2_hidden(esk3_2(esk10_0,X1),X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.02/1.19  fof(c_0_50, plain, ![X64, X65, X66, X68, X69, X70, X71, X73]:(((~r2_hidden(X66,X65)|r2_hidden(k4_tarski(esk5_3(X64,X65,X66),X66),X64)|X65!=k2_relat_1(X64))&(~r2_hidden(k4_tarski(X69,X68),X64)|r2_hidden(X68,X65)|X65!=k2_relat_1(X64)))&((~r2_hidden(esk6_2(X70,X71),X71)|~r2_hidden(k4_tarski(X73,esk6_2(X70,X71)),X70)|X71=k2_relat_1(X70))&(r2_hidden(esk6_2(X70,X71),X71)|r2_hidden(k4_tarski(esk7_2(X70,X71),esk6_2(X70,X71)),X70)|X71=k2_relat_1(X70)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 1.02/1.19  cnf(c_0_51, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 1.02/1.19  cnf(c_0_52, negated_conjecture, (k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)=k1_relat_1(esk10_0)|r2_hidden(esk3_2(esk10_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))), inference(ef,[status(thm)],[c_0_49])).
% 1.02/1.19  cnf(c_0_53, plain, (X2=k1_relat_1(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(k4_tarski(esk3_2(X1,X2),X3),X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.02/1.19  cnf(c_0_54, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.02/1.19  cnf(c_0_55, plain, (r2_hidden(esk6_2(X1,X2),X2)|r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.02/1.19  cnf(c_0_56, negated_conjecture, (k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)=k1_relat_1(esk10_0)|r2_hidden(k4_tarski(esk3_2(esk10_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),X1),k2_zfmisc_1(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.02/1.19  cnf(c_0_57, negated_conjecture, (k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)=k1_relat_1(esk10_0)|~r2_hidden(k4_tarski(esk3_2(esk10_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)),X1),esk10_0)), inference(spm,[status(thm)],[c_0_53, c_0_52])).
% 1.02/1.19  cnf(c_0_58, negated_conjecture, (k1_relat_1(esk10_0)!=k1_tarski(esk8_0)|k2_relat_1(esk10_0)!=k1_tarski(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.02/1.19  cnf(c_0_59, plain, (X1=k2_relat_1(k2_zfmisc_1(X2,X3))|r2_hidden(esk6_2(k2_zfmisc_1(X2,X3),X1),X1)|r2_hidden(esk6_2(k2_zfmisc_1(X2,X3),X1),X3)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 1.02/1.19  cnf(c_0_60, negated_conjecture, (k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)=k1_relat_1(esk10_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_41]), c_0_57])).
% 1.02/1.19  cnf(c_0_61, negated_conjecture, (k1_relat_1(esk10_0)!=k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)|k2_relat_1(esk10_0)!=k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31])).
% 1.02/1.19  cnf(c_0_62, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r1_tarski(k2_zfmisc_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),X3)), inference(spm,[status(thm)],[c_0_43, c_0_37])).
% 1.02/1.19  cnf(c_0_63, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|r2_hidden(esk6_2(k2_zfmisc_1(X1,X2),X2),X2)), inference(ef,[status(thm)],[c_0_59])).
% 1.02/1.19  cnf(c_0_64, negated_conjecture, (k2_zfmisc_1(k1_relat_1(esk10_0),k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))=esk10_0), inference(rw,[status(thm)],[c_0_41, c_0_60])).
% 1.02/1.19  cnf(c_0_65, negated_conjecture, (k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)!=k2_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_60])])).
% 1.02/1.19  cnf(c_0_66, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.02/1.19  cnf(c_0_67, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk9_0),X1)|~r1_tarski(esk10_0,X1)), inference(spm,[status(thm)],[c_0_62, c_0_41])).
% 1.02/1.19  cnf(c_0_68, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk6_2(X1,X2),X2)|~r2_hidden(k4_tarski(X3,esk6_2(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.02/1.19  cnf(c_0_69, negated_conjecture, (r2_hidden(esk6_2(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 1.02/1.19  cnf(c_0_70, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_66])).
% 1.02/1.19  cnf(c_0_71, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk9_0),esk10_0)), inference(spm,[status(thm)],[c_0_67, c_0_44])).
% 1.02/1.19  cnf(c_0_72, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|~r2_hidden(k4_tarski(X3,esk6_2(k2_zfmisc_1(X1,X2),X2)),k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_68, c_0_63])).
% 1.02/1.19  cnf(c_0_73, negated_conjecture, (r2_hidden(k4_tarski(X1,esk6_2(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))),k2_zfmisc_1(X2,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_69])).
% 1.02/1.19  cnf(c_0_74, negated_conjecture, (r2_hidden(esk8_0,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 1.02/1.19  cnf(c_0_75, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk6_2(esk10_0,k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))),esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_64]), c_0_65])).
% 1.02/1.19  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_64]), c_0_75]), ['proof']).
% 1.02/1.19  # SZS output end CNFRefutation
% 1.02/1.19  # Proof object total steps             : 77
% 1.02/1.19  # Proof object clause steps            : 48
% 1.02/1.19  # Proof object formula steps           : 29
% 1.02/1.19  # Proof object conjectures             : 23
% 1.02/1.19  # Proof object clause conjectures      : 20
% 1.02/1.19  # Proof object formula conjectures     : 3
% 1.02/1.19  # Proof object initial clauses used    : 20
% 1.02/1.19  # Proof object initial formulas used   : 14
% 1.02/1.19  # Proof object generating inferences   : 19
% 1.02/1.19  # Proof object simplifying inferences  : 57
% 1.02/1.19  # Training examples: 0 positive, 0 negative
% 1.02/1.19  # Parsed axioms                        : 16
% 1.02/1.19  # Removed by relevancy pruning/SinE    : 0
% 1.02/1.19  # Initial clauses                      : 34
% 1.02/1.19  # Removed in clause preprocessing      : 7
% 1.02/1.19  # Initial clauses in saturation        : 27
% 1.02/1.19  # Processed clauses                    : 836
% 1.02/1.19  # ...of these trivial                  : 1
% 1.02/1.19  # ...subsumed                          : 23
% 1.02/1.19  # ...remaining for further processing  : 812
% 1.02/1.19  # Other redundant clauses eliminated   : 7
% 1.02/1.19  # Clauses deleted for lack of memory   : 0
% 1.02/1.19  # Backward-subsumed                    : 0
% 1.02/1.19  # Backward-rewritten                   : 26
% 1.02/1.19  # Generated clauses                    : 116586
% 1.02/1.19  # ...of the previous two non-trivial   : 115999
% 1.02/1.19  # Contextual simplify-reflections      : 1
% 1.02/1.19  # Paramodulations                      : 116565
% 1.02/1.19  # Factorizations                       : 12
% 1.02/1.19  # Equation resolutions                 : 7
% 1.02/1.19  # Propositional unsat checks           : 0
% 1.02/1.19  #    Propositional check models        : 0
% 1.02/1.19  #    Propositional check unsatisfiable : 0
% 1.02/1.19  #    Propositional clauses             : 0
% 1.02/1.19  #    Propositional clauses after purity: 0
% 1.02/1.19  #    Propositional unsat core size     : 0
% 1.02/1.19  #    Propositional preprocessing time  : 0.000
% 1.02/1.19  #    Propositional encoding time       : 0.000
% 1.02/1.19  #    Propositional solver time         : 0.000
% 1.02/1.19  #    Success case prop preproc time    : 0.000
% 1.02/1.19  #    Success case prop encoding time   : 0.000
% 1.02/1.19  #    Success case prop solver time     : 0.000
% 1.02/1.19  # Current number of processed clauses  : 751
% 1.02/1.19  #    Positive orientable unit clauses  : 440
% 1.02/1.19  #    Positive unorientable unit clauses: 0
% 1.02/1.19  #    Negative unit clauses             : 4
% 1.02/1.19  #    Non-unit-clauses                  : 307
% 1.02/1.19  # Current number of unprocessed clauses: 115042
% 1.02/1.19  # ...number of literals in the above   : 156577
% 1.02/1.19  # Current number of archived formulas  : 0
% 1.02/1.19  # Current number of archived clauses   : 61
% 1.02/1.19  # Clause-clause subsumption calls (NU) : 24133
% 1.02/1.19  # Rec. Clause-clause subsumption calls : 17424
% 1.02/1.19  # Non-unit clause-clause subsumptions  : 23
% 1.02/1.19  # Unit Clause-clause subsumption calls : 18209
% 1.02/1.19  # Rewrite failures with RHS unbound    : 0
% 1.02/1.19  # BW rewrite match attempts            : 5840
% 1.02/1.19  # BW rewrite match successes           : 5
% 1.02/1.19  # Condensation attempts                : 0
% 1.02/1.19  # Condensation successes               : 0
% 1.02/1.19  # Termbank termtop insertions          : 3065086
% 1.02/1.20  
% 1.02/1.20  # -------------------------------------------------
% 1.02/1.20  # User time                : 0.818 s
% 1.02/1.20  # System time              : 0.050 s
% 1.02/1.20  # Total time               : 0.868 s
% 1.02/1.20  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
