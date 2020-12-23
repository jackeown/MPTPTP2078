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
% DateTime   : Thu Dec  3 10:51:33 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 157 expanded)
%              Number of clauses        :   39 (  72 expanded)
%              Number of leaves         :   10 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  207 ( 574 expanded)
%              Number of equality atoms :   41 ( 117 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_10,plain,(
    ! [X17,X18,X20,X21,X22] :
      ( ( r1_xboole_0(X17,X18)
        | r2_hidden(esk2_2(X17,X18),k3_xboole_0(X17,X18)) )
      & ( ~ r2_hidden(X22,k3_xboole_0(X20,X21))
        | ~ r1_xboole_0(X20,X21) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_11,plain,(
    ! [X51,X52,X53,X55] :
      ( ( r2_hidden(esk10_3(X51,X52,X53),k2_relat_1(X53))
        | ~ r2_hidden(X51,k10_relat_1(X53,X52))
        | ~ v1_relat_1(X53) )
      & ( r2_hidden(k4_tarski(X51,esk10_3(X51,X52,X53)),X53)
        | ~ r2_hidden(X51,k10_relat_1(X53,X52))
        | ~ v1_relat_1(X53) )
      & ( r2_hidden(esk10_3(X51,X52,X53),X52)
        | ~ r2_hidden(X51,k10_relat_1(X53,X52))
        | ~ v1_relat_1(X53) )
      & ( ~ r2_hidden(X55,k2_relat_1(X53))
        | ~ r2_hidden(k4_tarski(X51,X55),X53)
        | ~ r2_hidden(X55,X52)
        | r2_hidden(X51,k10_relat_1(X53,X52))
        | ~ v1_relat_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( r2_hidden(esk10_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X56,X57] :
      ( ~ v1_relat_1(X57)
      | k10_relat_1(X57,X56) = k10_relat_1(X57,k3_xboole_0(k2_relat_1(X57),X56)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

fof(c_0_15,plain,(
    ! [X28,X29,X30,X31,X33,X34,X35,X36,X38] :
      ( ( r2_hidden(k4_tarski(X31,esk4_4(X28,X29,X30,X31)),X28)
        | ~ r2_hidden(X31,X30)
        | X30 != k10_relat_1(X28,X29)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(esk4_4(X28,X29,X30,X31),X29)
        | ~ r2_hidden(X31,X30)
        | X30 != k10_relat_1(X28,X29)
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(X33,X34),X28)
        | ~ r2_hidden(X34,X29)
        | r2_hidden(X33,X30)
        | X30 != k10_relat_1(X28,X29)
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(esk5_3(X28,X35,X36),X36)
        | ~ r2_hidden(k4_tarski(esk5_3(X28,X35,X36),X38),X28)
        | ~ r2_hidden(X38,X35)
        | X36 = k10_relat_1(X28,X35)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(k4_tarski(esk5_3(X28,X35,X36),esk6_3(X28,X35,X36)),X28)
        | r2_hidden(esk5_3(X28,X35,X36),X36)
        | X36 = k10_relat_1(X28,X35)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(esk6_3(X28,X35,X36),X35)
        | r2_hidden(esk5_3(X28,X35,X36),X36)
        | X36 = k10_relat_1(X28,X35)
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_16,plain,(
    ! [X40,X41,X42,X44,X45,X46,X47,X49] :
      ( ( ~ r2_hidden(X42,X41)
        | r2_hidden(k4_tarski(esk7_3(X40,X41,X42),X42),X40)
        | X41 != k2_relat_1(X40) )
      & ( ~ r2_hidden(k4_tarski(X45,X44),X40)
        | r2_hidden(X44,X41)
        | X41 != k2_relat_1(X40) )
      & ( ~ r2_hidden(esk8_2(X46,X47),X47)
        | ~ r2_hidden(k4_tarski(X49,esk8_2(X46,X47)),X46)
        | X47 = k2_relat_1(X46) )
      & ( r2_hidden(esk8_2(X46,X47),X47)
        | r2_hidden(k4_tarski(esk9_2(X46,X47),esk8_2(X46,X47)),X46)
        | X47 = k2_relat_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_17,plain,
    ( ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X4,k10_relat_1(X1,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X23] :
      ( X23 = k1_xboole_0
      | r2_hidden(esk3_1(X23),X23) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) )
    & ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_26,plain,(
    ! [X26,X27] :
      ( ~ r1_xboole_0(k1_tarski(X26),X27)
      | ~ r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_27,plain,(
    ! [X25] : r1_xboole_0(X25,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | ~ r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_36,plain,
    ( r2_hidden(esk7_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk12_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_32])]),c_0_38])).

cnf(c_0_41,plain,
    ( r2_hidden(esk10_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk10_3(X1,X2,esk12_0),esk11_0)
    | ~ r2_hidden(X1,k10_relat_1(esk12_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_32])])).

cnf(c_0_45,plain,
    ( r2_hidden(esk10_3(X1,k3_xboole_0(X2,X3),X4),X3)
    | ~ v1_relat_1(X4)
    | ~ r2_hidden(X1,k10_relat_1(X4,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_13])).

cnf(c_0_46,plain,
    ( r2_hidden(esk8_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk9_2(X1,X2),esk8_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_24])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(X1,k10_relat_1(esk12_0,k3_xboole_0(X2,esk11_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_32])])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk8_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_46]),c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( k10_relat_1(esk12_0,k3_xboole_0(X1,esk11_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,esk11_0))
    | ~ r2_hidden(X1,k2_relat_1(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_50]),c_0_32])]),c_0_38])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(X1,esk11_0)
    | ~ r2_hidden(esk2_2(X1,esk11_0),k2_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_37])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:11:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.47  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.029 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.47  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 0.19/0.47  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 0.19/0.47  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.19/0.47  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.47  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.47  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 0.19/0.47  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.19/0.47  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.47  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.47  fof(c_0_10, plain, ![X17, X18, X20, X21, X22]:((r1_xboole_0(X17,X18)|r2_hidden(esk2_2(X17,X18),k3_xboole_0(X17,X18)))&(~r2_hidden(X22,k3_xboole_0(X20,X21))|~r1_xboole_0(X20,X21))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.47  fof(c_0_11, plain, ![X51, X52, X53, X55]:((((r2_hidden(esk10_3(X51,X52,X53),k2_relat_1(X53))|~r2_hidden(X51,k10_relat_1(X53,X52))|~v1_relat_1(X53))&(r2_hidden(k4_tarski(X51,esk10_3(X51,X52,X53)),X53)|~r2_hidden(X51,k10_relat_1(X53,X52))|~v1_relat_1(X53)))&(r2_hidden(esk10_3(X51,X52,X53),X52)|~r2_hidden(X51,k10_relat_1(X53,X52))|~v1_relat_1(X53)))&(~r2_hidden(X55,k2_relat_1(X53))|~r2_hidden(k4_tarski(X51,X55),X53)|~r2_hidden(X55,X52)|r2_hidden(X51,k10_relat_1(X53,X52))|~v1_relat_1(X53))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.19/0.47  cnf(c_0_12, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.47  cnf(c_0_13, plain, (r2_hidden(esk10_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.47  fof(c_0_14, plain, ![X56, X57]:(~v1_relat_1(X57)|k10_relat_1(X57,X56)=k10_relat_1(X57,k3_xboole_0(k2_relat_1(X57),X56))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.19/0.47  fof(c_0_15, plain, ![X28, X29, X30, X31, X33, X34, X35, X36, X38]:((((r2_hidden(k4_tarski(X31,esk4_4(X28,X29,X30,X31)),X28)|~r2_hidden(X31,X30)|X30!=k10_relat_1(X28,X29)|~v1_relat_1(X28))&(r2_hidden(esk4_4(X28,X29,X30,X31),X29)|~r2_hidden(X31,X30)|X30!=k10_relat_1(X28,X29)|~v1_relat_1(X28)))&(~r2_hidden(k4_tarski(X33,X34),X28)|~r2_hidden(X34,X29)|r2_hidden(X33,X30)|X30!=k10_relat_1(X28,X29)|~v1_relat_1(X28)))&((~r2_hidden(esk5_3(X28,X35,X36),X36)|(~r2_hidden(k4_tarski(esk5_3(X28,X35,X36),X38),X28)|~r2_hidden(X38,X35))|X36=k10_relat_1(X28,X35)|~v1_relat_1(X28))&((r2_hidden(k4_tarski(esk5_3(X28,X35,X36),esk6_3(X28,X35,X36)),X28)|r2_hidden(esk5_3(X28,X35,X36),X36)|X36=k10_relat_1(X28,X35)|~v1_relat_1(X28))&(r2_hidden(esk6_3(X28,X35,X36),X35)|r2_hidden(esk5_3(X28,X35,X36),X36)|X36=k10_relat_1(X28,X35)|~v1_relat_1(X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.19/0.47  fof(c_0_16, plain, ![X40, X41, X42, X44, X45, X46, X47, X49]:(((~r2_hidden(X42,X41)|r2_hidden(k4_tarski(esk7_3(X40,X41,X42),X42),X40)|X41!=k2_relat_1(X40))&(~r2_hidden(k4_tarski(X45,X44),X40)|r2_hidden(X44,X41)|X41!=k2_relat_1(X40)))&((~r2_hidden(esk8_2(X46,X47),X47)|~r2_hidden(k4_tarski(X49,esk8_2(X46,X47)),X46)|X47=k2_relat_1(X46))&(r2_hidden(esk8_2(X46,X47),X47)|r2_hidden(k4_tarski(esk9_2(X46,X47),esk8_2(X46,X47)),X46)|X47=k2_relat_1(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.47  cnf(c_0_17, plain, (~v1_relat_1(X1)|~r1_xboole_0(X2,X3)|~r2_hidden(X4,k10_relat_1(X1,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.47  cnf(c_0_18, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.47  fof(c_0_19, plain, ![X23]:(X23=k1_xboole_0|r2_hidden(esk3_1(X23),X23)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.47  fof(c_0_20, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.19/0.47  cnf(c_0_21, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  cnf(c_0_22, plain, (r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  cnf(c_0_23, plain, (~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)|~r2_hidden(X3,k10_relat_1(X1,X2))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.47  cnf(c_0_24, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.47  fof(c_0_25, negated_conjecture, (v1_relat_1(esk12_0)&((k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0))&(k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.19/0.47  fof(c_0_26, plain, ![X26, X27]:(~r1_xboole_0(k1_tarski(X26),X27)|~r2_hidden(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.19/0.47  fof(c_0_27, plain, ![X25]:r1_xboole_0(X25,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.47  cnf(c_0_28, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.47  cnf(c_0_29, plain, (r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_30, plain, (k10_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.47  cnf(c_0_31, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.47  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.47  cnf(c_0_33, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.47  cnf(c_0_34, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.47  fof(c_0_35, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7))&(r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k3_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k3_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))&(r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.47  cnf(c_0_36, plain, (r2_hidden(esk7_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.47  cnf(c_0_37, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.19/0.47  cnf(c_0_38, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.47  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.47  cnf(c_0_40, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk12_0))|~r2_hidden(X1,esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_32])]), c_0_38])).
% 0.19/0.47  cnf(c_0_41, plain, (r2_hidden(esk10_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.47  cnf(c_0_42, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_39])).
% 0.19/0.47  cnf(c_0_43, plain, (~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_38, c_0_29])).
% 0.19/0.47  cnf(c_0_44, negated_conjecture, (~r2_hidden(esk10_3(X1,X2,esk12_0),esk11_0)|~r2_hidden(X1,k10_relat_1(esk12_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_32])])).
% 0.19/0.47  cnf(c_0_45, plain, (r2_hidden(esk10_3(X1,k3_xboole_0(X2,X3),X4),X3)|~v1_relat_1(X4)|~r2_hidden(X1,k10_relat_1(X4,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_42, c_0_13])).
% 0.19/0.47  cnf(c_0_46, plain, (r2_hidden(esk8_2(X1,X2),X2)|r2_hidden(k4_tarski(esk9_2(X1,X2),esk8_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  cnf(c_0_47, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_24])).
% 0.19/0.47  cnf(c_0_48, negated_conjecture, (~r2_hidden(X1,k10_relat_1(esk12_0,k3_xboole_0(X2,esk11_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_32])])).
% 0.19/0.47  cnf(c_0_49, plain, (X1=k1_xboole_0|r2_hidden(esk8_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_46]), c_0_47])).
% 0.19/0.47  cnf(c_0_50, negated_conjecture, (k10_relat_1(esk12_0,k3_xboole_0(X1,esk11_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.47  cnf(c_0_51, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.47  cnf(c_0_52, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(X2,esk11_0))|~r2_hidden(X1,k2_relat_1(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_50]), c_0_32])]), c_0_38])).
% 0.19/0.47  cnf(c_0_53, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.47  cnf(c_0_54, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_51])).
% 0.19/0.47  cnf(c_0_55, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.47  cnf(c_0_56, negated_conjecture, (r1_xboole_0(X1,esk11_0)|~r2_hidden(esk2_2(X1,esk11_0),k2_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.47  cnf(c_0_57, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_54, c_0_53])).
% 0.19/0.47  cnf(c_0_58, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_37])])).
% 0.19/0.47  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 60
% 0.19/0.47  # Proof object clause steps            : 39
% 0.19/0.47  # Proof object formula steps           : 21
% 0.19/0.47  # Proof object conjectures             : 15
% 0.19/0.47  # Proof object clause conjectures      : 12
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 16
% 0.19/0.47  # Proof object initial formulas used   : 10
% 0.19/0.47  # Proof object generating inferences   : 18
% 0.19/0.47  # Proof object simplifying inferences  : 20
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 11
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 31
% 0.19/0.47  # Removed in clause preprocessing      : 0
% 0.19/0.47  # Initial clauses in saturation        : 31
% 0.19/0.47  # Processed clauses                    : 1569
% 0.19/0.47  # ...of these trivial                  : 0
% 0.19/0.47  # ...subsumed                          : 1308
% 0.19/0.47  # ...remaining for further processing  : 261
% 0.19/0.47  # Other redundant clauses eliminated   : 8
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 2
% 0.19/0.47  # Backward-rewritten                   : 12
% 0.19/0.47  # Generated clauses                    : 5416
% 0.19/0.47  # ...of the previous two non-trivial   : 4879
% 0.19/0.47  # Contextual simplify-reflections      : 0
% 0.19/0.47  # Paramodulations                      : 5401
% 0.19/0.47  # Factorizations                       : 7
% 0.19/0.47  # Equation resolutions                 : 8
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 209
% 0.19/0.47  #    Positive orientable unit clauses  : 12
% 0.19/0.47  #    Positive unorientable unit clauses: 0
% 0.19/0.47  #    Negative unit clauses             : 3
% 0.19/0.47  #    Non-unit-clauses                  : 194
% 0.19/0.47  # Current number of unprocessed clauses: 3283
% 0.19/0.47  # ...number of literals in the above   : 11407
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 44
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 13048
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 5867
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 780
% 0.19/0.47  # Unit Clause-clause subsumption calls : 60
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 5
% 0.19/0.47  # BW rewrite match successes           : 5
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 82777
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.119 s
% 0.19/0.47  # System time              : 0.008 s
% 0.19/0.47  # Total time               : 0.127 s
% 0.19/0.47  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
