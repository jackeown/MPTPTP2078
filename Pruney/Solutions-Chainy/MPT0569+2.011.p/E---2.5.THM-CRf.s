%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:34 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 126 expanded)
%              Number of clauses        :   33 (  58 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  194 ( 409 expanded)
%              Number of equality atoms :   43 (  99 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

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

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_10,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r1_xboole_0(X15,X16)
        | r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X20,k3_xboole_0(X18,X19))
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_11,plain,(
    ! [X21] :
      ( X21 = k1_xboole_0
      | r2_hidden(esk3_1(X21),X21) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_12,plain,(
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

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

fof(c_0_14,plain,(
    ! [X56,X57] :
      ( ~ v1_relat_1(X57)
      | k10_relat_1(X57,X56) = k10_relat_1(X57,k3_xboole_0(k2_relat_1(X57),X56)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X24,X25] :
      ( ~ r1_xboole_0(k1_tarski(X24),X25)
      | ~ r2_hidden(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_18,plain,(
    ! [X23] : r1_xboole_0(X23,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_19,plain,
    ( r2_hidden(esk10_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) )
    & ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_21,plain,(
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

fof(c_0_22,plain,(
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

cnf(c_0_23,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(esk10_3(esk3_1(k10_relat_1(X1,X2)),X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k10_relat_1(esk12_0,X1) = k1_xboole_0
    | r2_hidden(esk10_3(esk3_1(k10_relat_1(esk12_0,X1)),X1,esk12_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

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
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k10_relat_1(esk12_0,k1_xboole_0)
    | k10_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_28])])).

cnf(c_0_39,negated_conjecture,
    ( k10_relat_1(esk12_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( r2_hidden(esk7_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk12_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_28])]),c_0_33])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk12_0),X1)
    | ~ r2_hidden(esk2_2(k2_relat_1(esk12_0),X1),esk11_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_42])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic U_____100_C09_12_F1_SE_CS_SP_PS_S5PRR_RG_ND_S04AN
% 0.19/0.46  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.029 s
% 0.19/0.46  # Presaturation interreduction done
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.46  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.46  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.19/0.46  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.19/0.46  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 0.19/0.46  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.19/0.46  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.46  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 0.19/0.46  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.46  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.46  fof(c_0_10, plain, ![X15, X16, X18, X19, X20]:((r1_xboole_0(X15,X16)|r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)))&(~r2_hidden(X20,k3_xboole_0(X18,X19))|~r1_xboole_0(X18,X19))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.46  fof(c_0_11, plain, ![X21]:(X21=k1_xboole_0|r2_hidden(esk3_1(X21),X21)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.46  fof(c_0_12, plain, ![X51, X52, X53, X55]:((((r2_hidden(esk10_3(X51,X52,X53),k2_relat_1(X53))|~r2_hidden(X51,k10_relat_1(X53,X52))|~v1_relat_1(X53))&(r2_hidden(k4_tarski(X51,esk10_3(X51,X52,X53)),X53)|~r2_hidden(X51,k10_relat_1(X53,X52))|~v1_relat_1(X53)))&(r2_hidden(esk10_3(X51,X52,X53),X52)|~r2_hidden(X51,k10_relat_1(X53,X52))|~v1_relat_1(X53)))&(~r2_hidden(X55,k2_relat_1(X53))|~r2_hidden(k4_tarski(X51,X55),X53)|~r2_hidden(X55,X52)|r2_hidden(X51,k10_relat_1(X53,X52))|~v1_relat_1(X53))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.19/0.46  fof(c_0_13, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.19/0.46  fof(c_0_14, plain, ![X56, X57]:(~v1_relat_1(X57)|k10_relat_1(X57,X56)=k10_relat_1(X57,k3_xboole_0(k2_relat_1(X57),X56))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.19/0.46  cnf(c_0_15, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.46  cnf(c_0_16, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.46  fof(c_0_17, plain, ![X24, X25]:(~r1_xboole_0(k1_tarski(X24),X25)|~r2_hidden(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.19/0.46  fof(c_0_18, plain, ![X23]:r1_xboole_0(X23,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.46  cnf(c_0_19, plain, (r2_hidden(esk10_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.46  fof(c_0_20, negated_conjecture, (v1_relat_1(esk12_0)&((k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0))&(k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.19/0.46  fof(c_0_21, plain, ![X28, X29, X30, X31, X33, X34, X35, X36, X38]:((((r2_hidden(k4_tarski(X31,esk4_4(X28,X29,X30,X31)),X28)|~r2_hidden(X31,X30)|X30!=k10_relat_1(X28,X29)|~v1_relat_1(X28))&(r2_hidden(esk4_4(X28,X29,X30,X31),X29)|~r2_hidden(X31,X30)|X30!=k10_relat_1(X28,X29)|~v1_relat_1(X28)))&(~r2_hidden(k4_tarski(X33,X34),X28)|~r2_hidden(X34,X29)|r2_hidden(X33,X30)|X30!=k10_relat_1(X28,X29)|~v1_relat_1(X28)))&((~r2_hidden(esk5_3(X28,X35,X36),X36)|(~r2_hidden(k4_tarski(esk5_3(X28,X35,X36),X38),X28)|~r2_hidden(X38,X35))|X36=k10_relat_1(X28,X35)|~v1_relat_1(X28))&((r2_hidden(k4_tarski(esk5_3(X28,X35,X36),esk6_3(X28,X35,X36)),X28)|r2_hidden(esk5_3(X28,X35,X36),X36)|X36=k10_relat_1(X28,X35)|~v1_relat_1(X28))&(r2_hidden(esk6_3(X28,X35,X36),X35)|r2_hidden(esk5_3(X28,X35,X36),X36)|X36=k10_relat_1(X28,X35)|~v1_relat_1(X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.19/0.46  fof(c_0_22, plain, ![X40, X41, X42, X44, X45, X46, X47, X49]:(((~r2_hidden(X42,X41)|r2_hidden(k4_tarski(esk7_3(X40,X41,X42),X42),X40)|X41!=k2_relat_1(X40))&(~r2_hidden(k4_tarski(X45,X44),X40)|r2_hidden(X44,X41)|X41!=k2_relat_1(X40)))&((~r2_hidden(esk8_2(X46,X47),X47)|~r2_hidden(k4_tarski(X49,esk8_2(X46,X47)),X46)|X47=k2_relat_1(X46))&(r2_hidden(esk8_2(X46,X47),X47)|r2_hidden(k4_tarski(esk9_2(X46,X47),esk8_2(X46,X47)),X46)|X47=k2_relat_1(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.46  cnf(c_0_23, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.46  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.46  cnf(c_0_25, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.46  cnf(c_0_26, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.46  cnf(c_0_27, plain, (k10_relat_1(X1,X2)=k1_xboole_0|r2_hidden(esk10_3(esk3_1(k10_relat_1(X1,X2)),X2,X1),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_16])).
% 0.19/0.46  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.46  cnf(c_0_29, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.46  cnf(c_0_30, plain, (r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.46  cnf(c_0_31, plain, (k10_relat_1(X1,k1_xboole_0)=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.46  cnf(c_0_32, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.46  cnf(c_0_33, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.46  cnf(c_0_34, negated_conjecture, (k10_relat_1(esk12_0,X1)=k1_xboole_0|r2_hidden(esk10_3(esk3_1(k10_relat_1(esk12_0,X1)),X1,esk12_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.46  fof(c_0_35, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7))&(r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k3_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k3_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))&(r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.46  cnf(c_0_36, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_29])).
% 0.19/0.46  cnf(c_0_37, plain, (r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_30])).
% 0.19/0.46  cnf(c_0_38, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k10_relat_1(esk12_0,k1_xboole_0)|k10_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_28])])).
% 0.19/0.46  cnf(c_0_39, negated_conjecture, (k10_relat_1(esk12_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.46  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.46  cnf(c_0_41, plain, (r2_hidden(esk7_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.46  cnf(c_0_42, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])])).
% 0.19/0.46  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_40])).
% 0.19/0.46  cnf(c_0_44, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.46  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.46  cnf(c_0_46, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk12_0))|~r2_hidden(X1,esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_28])]), c_0_33])).
% 0.19/0.46  cnf(c_0_47, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.46  cnf(c_0_48, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_45])).
% 0.19/0.46  cnf(c_0_49, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.46  cnf(c_0_50, negated_conjecture, (r1_xboole_0(k2_relat_1(esk12_0),X1)|~r2_hidden(esk2_2(k2_relat_1(esk12_0),X1),esk11_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.46  cnf(c_0_51, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_48, c_0_44])).
% 0.19/0.46  cnf(c_0_52, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_42])])).
% 0.19/0.46  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 54
% 0.19/0.46  # Proof object clause steps            : 33
% 0.19/0.46  # Proof object formula steps           : 21
% 0.19/0.46  # Proof object conjectures             : 14
% 0.19/0.46  # Proof object clause conjectures      : 11
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 14
% 0.19/0.46  # Proof object initial formulas used   : 10
% 0.19/0.46  # Proof object generating inferences   : 13
% 0.19/0.46  # Proof object simplifying inferences  : 14
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 11
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 30
% 0.19/0.46  # Removed in clause preprocessing      : 0
% 0.19/0.46  # Initial clauses in saturation        : 30
% 0.19/0.46  # Processed clauses                    : 1243
% 0.19/0.46  # ...of these trivial                  : 2
% 0.19/0.46  # ...subsumed                          : 982
% 0.19/0.46  # ...remaining for further processing  : 259
% 0.19/0.46  # Other redundant clauses eliminated   : 8
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 1
% 0.19/0.46  # Backward-rewritten                   : 6
% 0.19/0.46  # Generated clauses                    : 4762
% 0.19/0.46  # ...of the previous two non-trivial   : 3789
% 0.19/0.46  # Contextual simplify-reflections      : 0
% 0.19/0.46  # Paramodulations                      : 4747
% 0.19/0.46  # Factorizations                       : 7
% 0.19/0.46  # Equation resolutions                 : 8
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 215
% 0.19/0.46  #    Positive orientable unit clauses  : 12
% 0.19/0.46  #    Positive unorientable unit clauses: 0
% 0.19/0.46  #    Negative unit clauses             : 2
% 0.19/0.46  #    Non-unit-clauses                  : 201
% 0.19/0.46  # Current number of unprocessed clauses: 2598
% 0.19/0.46  # ...number of literals in the above   : 8333
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 36
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 14871
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 9361
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 699
% 0.19/0.46  # Unit Clause-clause subsumption calls : 7
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 3
% 0.19/0.46  # BW rewrite match successes           : 3
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 72685
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.109 s
% 0.19/0.46  # System time              : 0.009 s
% 0.19/0.46  # Total time               : 0.119 s
% 0.19/0.46  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
