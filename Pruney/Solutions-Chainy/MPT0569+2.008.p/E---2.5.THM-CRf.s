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
% DateTime   : Thu Dec  3 10:51:34 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 173 expanded)
%              Number of clauses        :   40 (  83 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  217 ( 512 expanded)
%              Number of equality atoms :   65 ( 202 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

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

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(c_0_12,plain,(
    ! [X23,X24] :
      ( ( k2_zfmisc_1(X23,X24) != k1_xboole_0
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0 )
      & ( X23 != k1_xboole_0
        | k2_zfmisc_1(X23,X24) = k1_xboole_0 )
      & ( X24 != k1_xboole_0
        | k2_zfmisc_1(X23,X24) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_13,plain,(
    ! [X25,X26] : ~ r2_hidden(X25,k2_zfmisc_1(X25,X26)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_14,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X52,X53,X54,X56] :
      ( ( r2_hidden(esk9_3(X52,X53,X54),k2_relat_1(X54))
        | ~ r2_hidden(X52,k10_relat_1(X54,X53))
        | ~ v1_relat_1(X54) )
      & ( r2_hidden(k4_tarski(X52,esk9_3(X52,X53,X54)),X54)
        | ~ r2_hidden(X52,k10_relat_1(X54,X53))
        | ~ v1_relat_1(X54) )
      & ( r2_hidden(esk9_3(X52,X53,X54),X53)
        | ~ r2_hidden(X52,k10_relat_1(X54,X53))
        | ~ v1_relat_1(X54) )
      & ( ~ r2_hidden(X56,k2_relat_1(X54))
        | ~ r2_hidden(k4_tarski(X52,X56),X54)
        | ~ r2_hidden(X56,X53)
        | r2_hidden(X52,k10_relat_1(X54,X53))
        | ~ v1_relat_1(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_18,plain,(
    ! [X41,X42,X43,X45,X46,X47,X48,X50] :
      ( ( ~ r2_hidden(X43,X42)
        | r2_hidden(k4_tarski(esk6_3(X41,X42,X43),X43),X41)
        | X42 != k2_relat_1(X41) )
      & ( ~ r2_hidden(k4_tarski(X46,X45),X41)
        | r2_hidden(X45,X42)
        | X42 != k2_relat_1(X41) )
      & ( ~ r2_hidden(esk7_2(X47,X48),X48)
        | ~ r2_hidden(k4_tarski(X50,esk7_2(X47,X48)),X47)
        | X48 = k2_relat_1(X47) )
      & ( r2_hidden(esk7_2(X47,X48),X48)
        | r2_hidden(k4_tarski(esk8_2(X47,X48),esk7_2(X47,X48)),X47)
        | X48 = k2_relat_1(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_19,plain,(
    ! [X57,X58] :
      ( ~ v1_relat_1(X58)
      | k10_relat_1(X58,X57) = k10_relat_1(X58,k3_xboole_0(k2_relat_1(X58),X57)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

fof(c_0_20,plain,(
    ! [X27,X28] : k1_setfam_1(k2_tarski(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_21,plain,(
    ! [X15,X16] :
      ( ( ~ r1_xboole_0(X15,X16)
        | k3_xboole_0(X15,X16) = k1_xboole_0 )
      & ( k3_xboole_0(X15,X16) != k1_xboole_0
        | r1_xboole_0(X15,X16) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(esk9_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk8_2(X1,X2),esk7_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

cnf(c_0_27,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk7_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_24]),c_0_25])).

fof(c_0_32,negated_conjecture,
    ( v1_relat_1(esk11_0)
    & ( k10_relat_1(esk11_0,esk10_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk11_0),esk10_0) )
    & ( k10_relat_1(esk11_0,esk10_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk11_0),esk10_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_33,plain,(
    ! [X29,X30,X31,X32,X34,X35,X36,X37,X39] :
      ( ( r2_hidden(k4_tarski(X32,esk3_4(X29,X30,X31,X32)),X29)
        | ~ r2_hidden(X32,X31)
        | X31 != k10_relat_1(X29,X30)
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(esk3_4(X29,X30,X31,X32),X30)
        | ~ r2_hidden(X32,X31)
        | X31 != k10_relat_1(X29,X30)
        | ~ v1_relat_1(X29) )
      & ( ~ r2_hidden(k4_tarski(X34,X35),X29)
        | ~ r2_hidden(X35,X30)
        | r2_hidden(X34,X31)
        | X31 != k10_relat_1(X29,X30)
        | ~ v1_relat_1(X29) )
      & ( ~ r2_hidden(esk4_3(X29,X36,X37),X37)
        | ~ r2_hidden(k4_tarski(esk4_3(X29,X36,X37),X39),X29)
        | ~ r2_hidden(X39,X36)
        | X37 = k10_relat_1(X29,X36)
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(k4_tarski(esk4_3(X29,X36,X37),esk5_3(X29,X36,X37)),X29)
        | r2_hidden(esk4_3(X29,X36,X37),X37)
        | X37 = k10_relat_1(X29,X36)
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(esk5_3(X29,X36,X37),X36)
        | r2_hidden(esk4_3(X29,X36,X37),X37)
        | X37 = k10_relat_1(X29,X36)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_34,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_36,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,plain,(
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

cnf(c_0_39,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k10_relat_1(esk11_0,esk10_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk11_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( k10_relat_1(esk11_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X17,X18,X20,X21,X22] :
      ( ( r1_xboole_0(X17,X18)
        | r2_hidden(esk2_2(X17,X18),k3_xboole_0(X17,X18)) )
      & ( ~ r2_hidden(X22,k3_xboole_0(X20,X21))
        | ~ r1_xboole_0(X20,X21) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k10_relat_1(esk11_0,esk10_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_37])])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_43,c_0_28])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,X2),esk11_0)
    | ~ r2_hidden(X2,esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_37])]),c_0_22])).

cnf(c_0_52,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_28])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_50,c_0_28])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk11_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2))) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( k10_relat_1(esk11_0,esk10_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk11_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk11_0),X1)
    | ~ r2_hidden(esk2_2(k2_relat_1(esk11_0),X1),esk10_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk11_0),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_46])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:17:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05AN
% 0.19/0.41  # and selection function PSelectComplexExceptUniqMaxPosHorn.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.029 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.41  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.19/0.41  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 0.19/0.41  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.41  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 0.19/0.41  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.41  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.41  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.19/0.41  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 0.19/0.41  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.19/0.41  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.41  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.41  fof(c_0_12, plain, ![X23, X24]:((k2_zfmisc_1(X23,X24)!=k1_xboole_0|(X23=k1_xboole_0|X24=k1_xboole_0))&((X23!=k1_xboole_0|k2_zfmisc_1(X23,X24)=k1_xboole_0)&(X24!=k1_xboole_0|k2_zfmisc_1(X23,X24)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.41  fof(c_0_13, plain, ![X25, X26]:~r2_hidden(X25,k2_zfmisc_1(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.19/0.41  cnf(c_0_14, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_15, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_16, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_14])).
% 0.19/0.41  fof(c_0_17, plain, ![X52, X53, X54, X56]:((((r2_hidden(esk9_3(X52,X53,X54),k2_relat_1(X54))|~r2_hidden(X52,k10_relat_1(X54,X53))|~v1_relat_1(X54))&(r2_hidden(k4_tarski(X52,esk9_3(X52,X53,X54)),X54)|~r2_hidden(X52,k10_relat_1(X54,X53))|~v1_relat_1(X54)))&(r2_hidden(esk9_3(X52,X53,X54),X53)|~r2_hidden(X52,k10_relat_1(X54,X53))|~v1_relat_1(X54)))&(~r2_hidden(X56,k2_relat_1(X54))|~r2_hidden(k4_tarski(X52,X56),X54)|~r2_hidden(X56,X53)|r2_hidden(X52,k10_relat_1(X54,X53))|~v1_relat_1(X54))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.19/0.41  fof(c_0_18, plain, ![X41, X42, X43, X45, X46, X47, X48, X50]:(((~r2_hidden(X43,X42)|r2_hidden(k4_tarski(esk6_3(X41,X42,X43),X43),X41)|X42!=k2_relat_1(X41))&(~r2_hidden(k4_tarski(X46,X45),X41)|r2_hidden(X45,X42)|X42!=k2_relat_1(X41)))&((~r2_hidden(esk7_2(X47,X48),X48)|~r2_hidden(k4_tarski(X50,esk7_2(X47,X48)),X47)|X48=k2_relat_1(X47))&(r2_hidden(esk7_2(X47,X48),X48)|r2_hidden(k4_tarski(esk8_2(X47,X48),esk7_2(X47,X48)),X47)|X48=k2_relat_1(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.41  fof(c_0_19, plain, ![X57, X58]:(~v1_relat_1(X58)|k10_relat_1(X58,X57)=k10_relat_1(X58,k3_xboole_0(k2_relat_1(X58),X57))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.19/0.41  fof(c_0_20, plain, ![X27, X28]:k1_setfam_1(k2_tarski(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.41  fof(c_0_21, plain, ![X15, X16]:((~r1_xboole_0(X15,X16)|k3_xboole_0(X15,X16)=k1_xboole_0)&(k3_xboole_0(X15,X16)!=k1_xboole_0|r1_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.41  cnf(c_0_22, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.41  cnf(c_0_23, plain, (r2_hidden(esk9_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_24, plain, (r2_hidden(esk7_2(X1,X2),X2)|r2_hidden(k4_tarski(esk8_2(X1,X2),esk7_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_25, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.19/0.41  fof(c_0_26, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.19/0.41  cnf(c_0_27, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_28, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_30, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.41  cnf(c_0_31, plain, (X1=k1_xboole_0|r2_hidden(esk7_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_24]), c_0_25])).
% 0.19/0.41  fof(c_0_32, negated_conjecture, (v1_relat_1(esk11_0)&((k10_relat_1(esk11_0,esk10_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk11_0),esk10_0))&(k10_relat_1(esk11_0,esk10_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk11_0),esk10_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.19/0.41  fof(c_0_33, plain, ![X29, X30, X31, X32, X34, X35, X36, X37, X39]:((((r2_hidden(k4_tarski(X32,esk3_4(X29,X30,X31,X32)),X29)|~r2_hidden(X32,X31)|X31!=k10_relat_1(X29,X30)|~v1_relat_1(X29))&(r2_hidden(esk3_4(X29,X30,X31,X32),X30)|~r2_hidden(X32,X31)|X31!=k10_relat_1(X29,X30)|~v1_relat_1(X29)))&(~r2_hidden(k4_tarski(X34,X35),X29)|~r2_hidden(X35,X30)|r2_hidden(X34,X31)|X31!=k10_relat_1(X29,X30)|~v1_relat_1(X29)))&((~r2_hidden(esk4_3(X29,X36,X37),X37)|(~r2_hidden(k4_tarski(esk4_3(X29,X36,X37),X39),X29)|~r2_hidden(X39,X36))|X37=k10_relat_1(X29,X36)|~v1_relat_1(X29))&((r2_hidden(k4_tarski(esk4_3(X29,X36,X37),esk5_3(X29,X36,X37)),X29)|r2_hidden(esk4_3(X29,X36,X37),X37)|X37=k10_relat_1(X29,X36)|~v1_relat_1(X29))&(r2_hidden(esk5_3(X29,X36,X37),X36)|r2_hidden(esk4_3(X29,X36,X37),X37)|X37=k10_relat_1(X29,X36)|~v1_relat_1(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.19/0.41  cnf(c_0_34, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.41  cnf(c_0_35, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_28])).
% 0.19/0.41  cnf(c_0_36, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.41  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.41  fof(c_0_38, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7))&(r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k3_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k3_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))&(r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.41  cnf(c_0_39, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.41  cnf(c_0_40, plain, (k10_relat_1(X1,k1_xboole_0)=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (k10_relat_1(esk11_0,esk10_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk11_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (k10_relat_1(esk11_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.41  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.41  fof(c_0_44, plain, ![X17, X18, X20, X21, X22]:((r1_xboole_0(X17,X18)|r2_hidden(esk2_2(X17,X18),k3_xboole_0(X17,X18)))&(~r2_hidden(X22,k3_xboole_0(X20,X21))|~r1_xboole_0(X20,X21))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.41  cnf(c_0_45, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_39])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (k10_relat_1(esk11_0,esk10_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_37])])).
% 0.19/0.41  cnf(c_0_47, plain, (r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_48, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_43, c_0_28])).
% 0.19/0.41  cnf(c_0_49, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.41  cnf(c_0_50, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (~r2_hidden(k4_tarski(X1,X2),esk11_0)|~r2_hidden(X2,esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_37])]), c_0_22])).
% 0.19/0.41  cnf(c_0_52, plain, (r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_47])).
% 0.19/0.41  cnf(c_0_53, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(er,[status(thm)],[c_0_48])).
% 0.19/0.41  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_49, c_0_28])).
% 0.19/0.41  cnf(c_0_55, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_50, c_0_28])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk11_0))|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.41  cnf(c_0_57, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.41  cnf(c_0_58, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2)))), inference(er,[status(thm)],[c_0_55])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (k10_relat_1(esk11_0,esk10_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk11_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (r1_xboole_0(k2_relat_1(esk11_0),X1)|~r2_hidden(esk2_2(k2_relat_1(esk11_0),X1),esk10_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.41  cnf(c_0_61, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_58, c_0_54])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk11_0),esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_46])])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 64
% 0.19/0.41  # Proof object clause steps            : 40
% 0.19/0.41  # Proof object formula steps           : 24
% 0.19/0.41  # Proof object conjectures             : 13
% 0.19/0.41  # Proof object clause conjectures      : 10
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 16
% 0.19/0.41  # Proof object initial formulas used   : 12
% 0.19/0.41  # Proof object generating inferences   : 13
% 0.19/0.41  # Proof object simplifying inferences  : 20
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 12
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 35
% 0.19/0.41  # Removed in clause preprocessing      : 1
% 0.19/0.41  # Initial clauses in saturation        : 34
% 0.19/0.41  # Processed clauses                    : 489
% 0.19/0.41  # ...of these trivial                  : 0
% 0.19/0.41  # ...subsumed                          : 285
% 0.19/0.41  # ...remaining for further processing  : 204
% 0.19/0.41  # Other redundant clauses eliminated   : 14
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 3
% 0.19/0.41  # Backward-rewritten                   : 12
% 0.19/0.41  # Generated clauses                    : 1886
% 0.19/0.41  # ...of the previous two non-trivial   : 1667
% 0.19/0.41  # Contextual simplify-reflections      : 0
% 0.19/0.41  # Paramodulations                      : 1860
% 0.19/0.41  # Factorizations                       : 12
% 0.19/0.41  # Equation resolutions                 : 14
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 146
% 0.19/0.41  #    Positive orientable unit clauses  : 14
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 3
% 0.19/0.41  #    Non-unit-clauses                  : 129
% 0.19/0.41  # Current number of unprocessed clauses: 1233
% 0.19/0.41  # ...number of literals in the above   : 4340
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 49
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 5205
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 2042
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 121
% 0.19/0.41  # Unit Clause-clause subsumption calls : 18
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 12
% 0.19/0.41  # BW rewrite match successes           : 6
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 33427
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.069 s
% 0.19/0.41  # System time              : 0.004 s
% 0.19/0.41  # Total time               : 0.073 s
% 0.19/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
