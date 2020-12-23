%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:35 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 193 expanded)
%              Number of clauses        :   46 (  92 expanded)
%              Number of leaves         :   11 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  229 ( 644 expanded)
%              Number of equality atoms :   60 ( 197 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

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

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_11,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r1_xboole_0(X15,X16)
        | r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X20,k3_xboole_0(X18,X19))
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X27,X28] : k1_setfam_1(k2_tarski(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X52,X53,X54,X56] :
      ( ( r2_hidden(esk10_3(X52,X53,X54),k2_relat_1(X54))
        | ~ r2_hidden(X52,k10_relat_1(X54,X53))
        | ~ v1_relat_1(X54) )
      & ( r2_hidden(k4_tarski(X52,esk10_3(X52,X53,X54)),X54)
        | ~ r2_hidden(X52,k10_relat_1(X54,X53))
        | ~ v1_relat_1(X54) )
      & ( r2_hidden(esk10_3(X52,X53,X54),X53)
        | ~ r2_hidden(X52,k10_relat_1(X54,X53))
        | ~ v1_relat_1(X54) )
      & ( ~ r2_hidden(X56,k2_relat_1(X54))
        | ~ r2_hidden(k4_tarski(X52,X56),X54)
        | ~ r2_hidden(X56,X53)
        | r2_hidden(X52,k10_relat_1(X54,X53))
        | ~ v1_relat_1(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_16,plain,(
    ! [X57,X58] :
      ( ~ v1_relat_1(X58)
      | k10_relat_1(X58,X57) = k10_relat_1(X58,k3_xboole_0(k2_relat_1(X58),X57)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

cnf(c_0_17,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(esk10_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X29,X30,X31,X32,X34,X35,X36,X37,X39] :
      ( ( r2_hidden(k4_tarski(X32,esk4_4(X29,X30,X31,X32)),X29)
        | ~ r2_hidden(X32,X31)
        | X31 != k10_relat_1(X29,X30)
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(esk4_4(X29,X30,X31,X32),X30)
        | ~ r2_hidden(X32,X31)
        | X31 != k10_relat_1(X29,X30)
        | ~ v1_relat_1(X29) )
      & ( ~ r2_hidden(k4_tarski(X34,X35),X29)
        | ~ r2_hidden(X35,X30)
        | r2_hidden(X34,X31)
        | X31 != k10_relat_1(X29,X30)
        | ~ v1_relat_1(X29) )
      & ( ~ r2_hidden(esk5_3(X29,X36,X37),X37)
        | ~ r2_hidden(k4_tarski(esk5_3(X29,X36,X37),X39),X29)
        | ~ r2_hidden(X39,X36)
        | X37 = k10_relat_1(X29,X36)
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(k4_tarski(esk5_3(X29,X36,X37),esk6_3(X29,X36,X37)),X29)
        | r2_hidden(esk5_3(X29,X36,X37),X37)
        | X37 = k10_relat_1(X29,X36)
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(esk6_3(X29,X36,X37),X36)
        | r2_hidden(esk5_3(X29,X36,X37),X37)
        | X37 = k10_relat_1(X29,X36)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_21,plain,(
    ! [X41,X42,X43,X45,X46,X47,X48,X50] :
      ( ( ~ r2_hidden(X43,X42)
        | r2_hidden(k4_tarski(esk7_3(X41,X42,X43),X43),X41)
        | X42 != k2_relat_1(X41) )
      & ( ~ r2_hidden(k4_tarski(X46,X45),X41)
        | r2_hidden(X45,X42)
        | X42 != k2_relat_1(X41) )
      & ( ~ r2_hidden(esk8_2(X47,X48),X48)
        | ~ r2_hidden(k4_tarski(X50,esk8_2(X47,X48)),X47)
        | X48 = k2_relat_1(X47) )
      & ( r2_hidden(esk8_2(X47,X48),X48)
        | r2_hidden(k4_tarski(esk9_2(X47,X48),esk8_2(X47,X48)),X47)
        | X48 = k2_relat_1(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_22,plain,
    ( ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X4,k10_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_14])).

fof(c_0_24,plain,(
    ! [X21] :
      ( X21 = k1_xboole_0
      | r2_hidden(esk3_1(X21),X21) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

fof(c_0_26,plain,(
    ! [X23,X24] :
      ( ( k2_zfmisc_1(X23,X24) != k1_xboole_0
        | X23 = k1_xboole_0
        | X24 = k1_xboole_0 )
      & ( X23 != k1_xboole_0
        | k2_zfmisc_1(X23,X24) = k1_xboole_0 )
      & ( X24 != k1_xboole_0
        | k2_zfmisc_1(X23,X24) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) )
    & ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_32,plain,(
    ! [X25,X26] : ~ r2_hidden(X25,k2_zfmisc_1(X25,X26)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
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

cnf(c_0_35,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(esk7_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_42,c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk12_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_39])]),c_0_45])).

cnf(c_0_48,plain,
    ( r2_hidden(esk10_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2))) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk10_3(X1,X2,esk12_0),esk11_0)
    | ~ r2_hidden(X1,k10_relat_1(esk12_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_39])])).

cnf(c_0_52,plain,
    ( r2_hidden(esk10_3(X1,k1_setfam_1(k2_tarski(X2,X3)),X4),X3)
    | ~ v1_relat_1(X4)
    | ~ r2_hidden(X1,k10_relat_1(X4,k1_setfam_1(k2_tarski(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_18])).

cnf(c_0_53,plain,
    ( r2_hidden(esk8_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk9_2(X1,X2),esk8_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_54,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(X1,k10_relat_1(esk12_0,k1_setfam_1(k2_tarski(X2,esk11_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_39])])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk8_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_53]),c_0_54])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_58,negated_conjecture,
    ( k10_relat_1(esk12_0,k1_setfam_1(k2_tarski(X1,esk11_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_57,c_0_14])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,esk11_0)))
    | ~ r2_hidden(X1,k2_relat_1(esk12_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_58]),c_0_39])]),c_0_45])).

cnf(c_0_62,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_59,c_0_14])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(X1,esk11_0)
    | ~ r2_hidden(esk2_2(X1,esk11_0),k2_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_44])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:29:35 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.45  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.45  #
% 0.18/0.45  # Preprocessing time       : 0.029 s
% 0.18/0.45  # Presaturation interreduction done
% 0.18/0.45  
% 0.18/0.45  # Proof found!
% 0.18/0.45  # SZS status Theorem
% 0.18/0.45  # SZS output start CNFRefutation
% 0.18/0.45  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.18/0.45  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.18/0.45  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.18/0.45  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 0.18/0.45  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 0.18/0.45  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.18/0.45  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.18/0.45  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.18/0.45  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.45  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.18/0.45  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.18/0.45  fof(c_0_11, plain, ![X15, X16, X18, X19, X20]:((r1_xboole_0(X15,X16)|r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)))&(~r2_hidden(X20,k3_xboole_0(X18,X19))|~r1_xboole_0(X18,X19))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.18/0.45  fof(c_0_12, plain, ![X27, X28]:k1_setfam_1(k2_tarski(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.18/0.45  cnf(c_0_13, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.45  cnf(c_0_14, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.45  fof(c_0_15, plain, ![X52, X53, X54, X56]:((((r2_hidden(esk10_3(X52,X53,X54),k2_relat_1(X54))|~r2_hidden(X52,k10_relat_1(X54,X53))|~v1_relat_1(X54))&(r2_hidden(k4_tarski(X52,esk10_3(X52,X53,X54)),X54)|~r2_hidden(X52,k10_relat_1(X54,X53))|~v1_relat_1(X54)))&(r2_hidden(esk10_3(X52,X53,X54),X53)|~r2_hidden(X52,k10_relat_1(X54,X53))|~v1_relat_1(X54)))&(~r2_hidden(X56,k2_relat_1(X54))|~r2_hidden(k4_tarski(X52,X56),X54)|~r2_hidden(X56,X53)|r2_hidden(X52,k10_relat_1(X54,X53))|~v1_relat_1(X54))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.18/0.45  fof(c_0_16, plain, ![X57, X58]:(~v1_relat_1(X58)|k10_relat_1(X58,X57)=k10_relat_1(X58,k3_xboole_0(k2_relat_1(X58),X57))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.18/0.45  cnf(c_0_17, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.18/0.45  cnf(c_0_18, plain, (r2_hidden(esk10_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.45  cnf(c_0_19, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.45  fof(c_0_20, plain, ![X29, X30, X31, X32, X34, X35, X36, X37, X39]:((((r2_hidden(k4_tarski(X32,esk4_4(X29,X30,X31,X32)),X29)|~r2_hidden(X32,X31)|X31!=k10_relat_1(X29,X30)|~v1_relat_1(X29))&(r2_hidden(esk4_4(X29,X30,X31,X32),X30)|~r2_hidden(X32,X31)|X31!=k10_relat_1(X29,X30)|~v1_relat_1(X29)))&(~r2_hidden(k4_tarski(X34,X35),X29)|~r2_hidden(X35,X30)|r2_hidden(X34,X31)|X31!=k10_relat_1(X29,X30)|~v1_relat_1(X29)))&((~r2_hidden(esk5_3(X29,X36,X37),X37)|(~r2_hidden(k4_tarski(esk5_3(X29,X36,X37),X39),X29)|~r2_hidden(X39,X36))|X37=k10_relat_1(X29,X36)|~v1_relat_1(X29))&((r2_hidden(k4_tarski(esk5_3(X29,X36,X37),esk6_3(X29,X36,X37)),X29)|r2_hidden(esk5_3(X29,X36,X37),X37)|X37=k10_relat_1(X29,X36)|~v1_relat_1(X29))&(r2_hidden(esk6_3(X29,X36,X37),X36)|r2_hidden(esk5_3(X29,X36,X37),X37)|X37=k10_relat_1(X29,X36)|~v1_relat_1(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.18/0.45  fof(c_0_21, plain, ![X41, X42, X43, X45, X46, X47, X48, X50]:(((~r2_hidden(X43,X42)|r2_hidden(k4_tarski(esk7_3(X41,X42,X43),X43),X41)|X42!=k2_relat_1(X41))&(~r2_hidden(k4_tarski(X46,X45),X41)|r2_hidden(X45,X42)|X42!=k2_relat_1(X41)))&((~r2_hidden(esk8_2(X47,X48),X48)|~r2_hidden(k4_tarski(X50,esk8_2(X47,X48)),X47)|X48=k2_relat_1(X47))&(r2_hidden(esk8_2(X47,X48),X48)|r2_hidden(k4_tarski(esk9_2(X47,X48),esk8_2(X47,X48)),X47)|X48=k2_relat_1(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.18/0.45  cnf(c_0_22, plain, (~v1_relat_1(X1)|~r1_xboole_0(X2,X3)|~r2_hidden(X4,k10_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.18/0.45  cnf(c_0_23, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_19, c_0_14])).
% 0.18/0.45  fof(c_0_24, plain, ![X21]:(X21=k1_xboole_0|r2_hidden(esk3_1(X21),X21)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.18/0.45  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.18/0.45  fof(c_0_26, plain, ![X23, X24]:((k2_zfmisc_1(X23,X24)!=k1_xboole_0|(X23=k1_xboole_0|X24=k1_xboole_0))&((X23!=k1_xboole_0|k2_zfmisc_1(X23,X24)=k1_xboole_0)&(X24!=k1_xboole_0|k2_zfmisc_1(X23,X24)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.45  cnf(c_0_27, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.45  cnf(c_0_28, plain, (r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.45  cnf(c_0_29, plain, (~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)|~r2_hidden(X3,k10_relat_1(X1,X2))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.45  cnf(c_0_30, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.45  fof(c_0_31, negated_conjecture, (v1_relat_1(esk12_0)&((k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0))&(k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.18/0.45  fof(c_0_32, plain, ![X25, X26]:~r2_hidden(X25,k2_zfmisc_1(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.18/0.45  cnf(c_0_33, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.45  fof(c_0_34, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7))&(r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k3_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k3_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))&(r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.18/0.45  cnf(c_0_35, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_27])).
% 0.18/0.45  cnf(c_0_36, plain, (r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_28])).
% 0.18/0.45  cnf(c_0_37, plain, (k10_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.45  cnf(c_0_38, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.45  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.45  cnf(c_0_40, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.45  cnf(c_0_41, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_33])).
% 0.18/0.45  cnf(c_0_42, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.45  cnf(c_0_43, plain, (r2_hidden(esk7_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.18/0.45  cnf(c_0_44, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.18/0.45  cnf(c_0_45, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.45  cnf(c_0_46, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_42, c_0_14])).
% 0.18/0.45  cnf(c_0_47, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk12_0))|~r2_hidden(X1,esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_39])]), c_0_45])).
% 0.18/0.45  cnf(c_0_48, plain, (r2_hidden(esk10_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.45  cnf(c_0_49, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X3,X2)))), inference(er,[status(thm)],[c_0_46])).
% 0.18/0.45  cnf(c_0_50, plain, (~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_45, c_0_36])).
% 0.18/0.45  cnf(c_0_51, negated_conjecture, (~r2_hidden(esk10_3(X1,X2,esk12_0),esk11_0)|~r2_hidden(X1,k10_relat_1(esk12_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_39])])).
% 0.18/0.45  cnf(c_0_52, plain, (r2_hidden(esk10_3(X1,k1_setfam_1(k2_tarski(X2,X3)),X4),X3)|~v1_relat_1(X4)|~r2_hidden(X1,k10_relat_1(X4,k1_setfam_1(k2_tarski(X2,X3))))), inference(spm,[status(thm)],[c_0_49, c_0_18])).
% 0.18/0.45  cnf(c_0_53, plain, (r2_hidden(esk8_2(X1,X2),X2)|r2_hidden(k4_tarski(esk9_2(X1,X2),esk8_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.45  cnf(c_0_54, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_30])).
% 0.18/0.45  cnf(c_0_55, negated_conjecture, (~r2_hidden(X1,k10_relat_1(esk12_0,k1_setfam_1(k2_tarski(X2,esk11_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_39])])).
% 0.18/0.45  cnf(c_0_56, plain, (X1=k1_xboole_0|r2_hidden(esk8_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_53]), c_0_54])).
% 0.18/0.45  cnf(c_0_57, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.45  cnf(c_0_58, negated_conjecture, (k10_relat_1(esk12_0,k1_setfam_1(k2_tarski(X1,esk11_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.18/0.45  cnf(c_0_59, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.45  cnf(c_0_60, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_57, c_0_14])).
% 0.18/0.45  cnf(c_0_61, negated_conjecture, (~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,esk11_0)))|~r2_hidden(X1,k2_relat_1(esk12_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_58]), c_0_39])]), c_0_45])).
% 0.18/0.45  cnf(c_0_62, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_59, c_0_14])).
% 0.18/0.45  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(er,[status(thm)],[c_0_60])).
% 0.18/0.45  cnf(c_0_64, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.45  cnf(c_0_65, negated_conjecture, (r1_xboole_0(X1,esk11_0)|~r2_hidden(esk2_2(X1,esk11_0),k2_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.18/0.45  cnf(c_0_66, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_63, c_0_62])).
% 0.18/0.45  cnf(c_0_67, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_44])])).
% 0.18/0.45  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), ['proof']).
% 0.18/0.45  # SZS output end CNFRefutation
% 0.18/0.45  # Proof object total steps             : 69
% 0.18/0.45  # Proof object clause steps            : 46
% 0.18/0.45  # Proof object formula steps           : 23
% 0.18/0.45  # Proof object conjectures             : 15
% 0.18/0.45  # Proof object clause conjectures      : 12
% 0.18/0.45  # Proof object formula conjectures     : 3
% 0.18/0.45  # Proof object initial clauses used    : 17
% 0.18/0.45  # Proof object initial formulas used   : 11
% 0.18/0.45  # Proof object generating inferences   : 18
% 0.18/0.45  # Proof object simplifying inferences  : 26
% 0.18/0.45  # Training examples: 0 positive, 0 negative
% 0.18/0.45  # Parsed axioms                        : 11
% 0.18/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.45  # Initial clauses                      : 32
% 0.18/0.45  # Removed in clause preprocessing      : 1
% 0.18/0.45  # Initial clauses in saturation        : 31
% 0.18/0.45  # Processed clauses                    : 1349
% 0.18/0.45  # ...of these trivial                  : 0
% 0.18/0.45  # ...subsumed                          : 1111
% 0.18/0.45  # ...remaining for further processing  : 238
% 0.18/0.45  # Other redundant clauses eliminated   : 10
% 0.18/0.45  # Clauses deleted for lack of memory   : 0
% 0.18/0.45  # Backward-subsumed                    : 3
% 0.18/0.45  # Backward-rewritten                   : 8
% 0.18/0.45  # Generated clauses                    : 4481
% 0.18/0.45  # ...of the previous two non-trivial   : 4032
% 0.18/0.45  # Contextual simplify-reflections      : 0
% 0.18/0.45  # Paramodulations                      : 4464
% 0.18/0.45  # Factorizations                       : 7
% 0.18/0.45  # Equation resolutions                 : 10
% 0.18/0.45  # Propositional unsat checks           : 0
% 0.18/0.45  #    Propositional check models        : 0
% 0.18/0.45  #    Propositional check unsatisfiable : 0
% 0.18/0.45  #    Propositional clauses             : 0
% 0.18/0.45  #    Propositional clauses after purity: 0
% 0.18/0.45  #    Propositional unsat core size     : 0
% 0.18/0.45  #    Propositional preprocessing time  : 0.000
% 0.18/0.45  #    Propositional encoding time       : 0.000
% 0.18/0.45  #    Propositional solver time         : 0.000
% 0.18/0.45  #    Success case prop preproc time    : 0.000
% 0.18/0.45  #    Success case prop encoding time   : 0.000
% 0.18/0.45  #    Success case prop solver time     : 0.000
% 0.18/0.45  # Current number of processed clauses  : 187
% 0.18/0.45  #    Positive orientable unit clauses  : 12
% 0.18/0.45  #    Positive unorientable unit clauses: 0
% 0.18/0.45  #    Negative unit clauses             : 3
% 0.18/0.45  #    Non-unit-clauses                  : 172
% 0.18/0.45  # Current number of unprocessed clauses: 2688
% 0.18/0.45  # ...number of literals in the above   : 9876
% 0.18/0.45  # Current number of archived formulas  : 0
% 0.18/0.45  # Current number of archived clauses   : 42
% 0.18/0.45  # Clause-clause subsumption calls (NU) : 11804
% 0.18/0.45  # Rec. Clause-clause subsumption calls : 5218
% 0.18/0.45  # Non-unit clause-clause subsumptions  : 742
% 0.18/0.45  # Unit Clause-clause subsumption calls : 86
% 0.18/0.45  # Rewrite failures with RHS unbound    : 0
% 0.18/0.45  # BW rewrite match attempts            : 6
% 0.18/0.45  # BW rewrite match successes           : 5
% 0.18/0.45  # Condensation attempts                : 0
% 0.18/0.45  # Condensation successes               : 0
% 0.18/0.45  # Termbank termtop insertions          : 70142
% 0.18/0.45  
% 0.18/0.45  # -------------------------------------------------
% 0.18/0.45  # User time                : 0.110 s
% 0.18/0.45  # System time              : 0.006 s
% 0.18/0.45  # Total time               : 0.116 s
% 0.18/0.45  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
