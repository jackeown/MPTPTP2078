%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 146 expanded)
%              Number of clauses        :   36 (  68 expanded)
%              Number of leaves         :   11 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  189 ( 469 expanded)
%              Number of equality atoms :   35 (  87 expanded)
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

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

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

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_11,plain,(
    ! [X12,X13,X15,X16,X17] :
      ( ( r1_xboole_0(X12,X13)
        | r2_hidden(esk2_2(X12,X13),k3_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X17,k3_xboole_0(X15,X16))
        | ~ r1_xboole_0(X15,X16) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X21,X22] : k1_setfam_1(k2_tarski(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X46,X47,X48,X50] :
      ( ( r2_hidden(esk9_3(X46,X47,X48),k2_relat_1(X48))
        | ~ r2_hidden(X46,k10_relat_1(X48,X47))
        | ~ v1_relat_1(X48) )
      & ( r2_hidden(k4_tarski(X46,esk9_3(X46,X47,X48)),X48)
        | ~ r2_hidden(X46,k10_relat_1(X48,X47))
        | ~ v1_relat_1(X48) )
      & ( r2_hidden(esk9_3(X46,X47,X48),X47)
        | ~ r2_hidden(X46,k10_relat_1(X48,X47))
        | ~ v1_relat_1(X48) )
      & ( ~ r2_hidden(X50,k2_relat_1(X48))
        | ~ r2_hidden(k4_tarski(X46,X50),X48)
        | ~ r2_hidden(X50,X47)
        | r2_hidden(X46,k10_relat_1(X48,X47))
        | ~ v1_relat_1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_16,plain,(
    ! [X51,X52] :
      ( ~ v1_relat_1(X52)
      | k10_relat_1(X52,X51) = k10_relat_1(X52,k3_xboole_0(k2_relat_1(X52),X51)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

cnf(c_0_17,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(esk9_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,k1_setfam_1(k2_tarski(X3,X4))))
    | ~ r1_xboole_0(X3,X4) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_14])).

fof(c_0_22,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_xboole_0(X6,X7) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | r1_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

cnf(c_0_24,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,negated_conjecture,
    ( v1_relat_1(esk11_0)
    & ( k10_relat_1(esk11_0,esk10_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk11_0),esk10_0) )
    & ( k10_relat_1(esk11_0,esk10_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk11_0),esk10_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_27,plain,(
    ! [X19,X20] :
      ( ~ r1_xboole_0(k1_tarski(X19),X20)
      | ~ r2_hidden(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_28,plain,(
    ! [X18] : r1_xboole_0(X18,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_29,plain,(
    ! [X23,X24,X25,X26,X28,X29,X30,X31,X33] :
      ( ( r2_hidden(k4_tarski(X26,esk3_4(X23,X24,X25,X26)),X23)
        | ~ r2_hidden(X26,X25)
        | X25 != k10_relat_1(X23,X24)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk3_4(X23,X24,X25,X26),X24)
        | ~ r2_hidden(X26,X25)
        | X25 != k10_relat_1(X23,X24)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(X28,X29),X23)
        | ~ r2_hidden(X29,X24)
        | r2_hidden(X28,X25)
        | X25 != k10_relat_1(X23,X24)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(esk4_3(X23,X30,X31),X31)
        | ~ r2_hidden(k4_tarski(esk4_3(X23,X30,X31),X33),X23)
        | ~ r2_hidden(X33,X30)
        | X31 = k10_relat_1(X23,X30)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(esk4_3(X23,X30,X31),esk5_3(X23,X30,X31)),X23)
        | r2_hidden(esk4_3(X23,X30,X31),X31)
        | X31 = k10_relat_1(X23,X30)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk5_3(X23,X30,X31),X30)
        | r2_hidden(esk4_3(X23,X30,X31),X31)
        | X31 = k10_relat_1(X23,X30)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_30,plain,(
    ! [X35,X36,X37,X39,X40,X41,X42,X44] :
      ( ( ~ r2_hidden(X37,X36)
        | r2_hidden(k4_tarski(esk6_3(X35,X36,X37),X37),X35)
        | X36 != k2_relat_1(X35) )
      & ( ~ r2_hidden(k4_tarski(X40,X39),X35)
        | r2_hidden(X39,X36)
        | X36 != k2_relat_1(X35) )
      & ( ~ r2_hidden(esk7_2(X41,X42),X42)
        | ~ r2_hidden(k4_tarski(X44,esk7_2(X41,X42)),X41)
        | X42 = k2_relat_1(X41) )
      & ( r2_hidden(esk7_2(X41,X42),X42)
        | r2_hidden(k4_tarski(esk8_2(X41,X42),esk7_2(X41,X42)),X41)
        | X42 = k2_relat_1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(k2_relat_1(X2),X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k10_relat_1(esk11_0,esk10_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk11_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k10_relat_1(esk11_0,esk10_0) = k1_xboole_0
    | r1_xboole_0(X1,k10_relat_1(esk11_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk8_2(X1,X2),esk7_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k10_relat_1(esk11_0,esk10_0) = k1_xboole_0
    | ~ r2_hidden(X1,k10_relat_1(esk11_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_38])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk7_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_46,plain,
    ( r2_hidden(esk6_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( k10_relat_1(esk11_0,esk10_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk11_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_33])]),c_0_39])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( r1_xboole_0(X1,k2_relat_1(esk11_0))
    | ~ r2_hidden(esk1_2(X1,k2_relat_1(esk11_0)),esk10_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_25])).

cnf(c_0_53,negated_conjecture,
    ( k10_relat_1(esk11_0,esk10_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk11_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_25])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(esk10_0,k2_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk11_0),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_47])])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.50  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.029 s
% 0.20/0.50  # Presaturation interreduction done
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.50  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.50  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.20/0.50  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 0.20/0.50  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.50  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.20/0.50  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.20/0.50  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.50  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 0.20/0.50  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.20/0.50  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.50  fof(c_0_11, plain, ![X12, X13, X15, X16, X17]:((r1_xboole_0(X12,X13)|r2_hidden(esk2_2(X12,X13),k3_xboole_0(X12,X13)))&(~r2_hidden(X17,k3_xboole_0(X15,X16))|~r1_xboole_0(X15,X16))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.50  fof(c_0_12, plain, ![X21, X22]:k1_setfam_1(k2_tarski(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.50  cnf(c_0_13, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.50  cnf(c_0_14, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.50  fof(c_0_15, plain, ![X46, X47, X48, X50]:((((r2_hidden(esk9_3(X46,X47,X48),k2_relat_1(X48))|~r2_hidden(X46,k10_relat_1(X48,X47))|~v1_relat_1(X48))&(r2_hidden(k4_tarski(X46,esk9_3(X46,X47,X48)),X48)|~r2_hidden(X46,k10_relat_1(X48,X47))|~v1_relat_1(X48)))&(r2_hidden(esk9_3(X46,X47,X48),X47)|~r2_hidden(X46,k10_relat_1(X48,X47))|~v1_relat_1(X48)))&(~r2_hidden(X50,k2_relat_1(X48))|~r2_hidden(k4_tarski(X46,X50),X48)|~r2_hidden(X50,X47)|r2_hidden(X46,k10_relat_1(X48,X47))|~v1_relat_1(X48))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.20/0.50  fof(c_0_16, plain, ![X51, X52]:(~v1_relat_1(X52)|k10_relat_1(X52,X51)=k10_relat_1(X52,k3_xboole_0(k2_relat_1(X52),X51))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.20/0.50  cnf(c_0_17, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.50  cnf(c_0_18, plain, (r2_hidden(esk9_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.50  cnf(c_0_19, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_20, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,k1_setfam_1(k2_tarski(X3,X4))))|~r1_xboole_0(X3,X4)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.50  cnf(c_0_21, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_19, c_0_14])).
% 0.20/0.50  fof(c_0_22, plain, ![X6, X7, X9, X10, X11]:(((r2_hidden(esk1_2(X6,X7),X6)|r1_xboole_0(X6,X7))&(r2_hidden(esk1_2(X6,X7),X7)|r1_xboole_0(X6,X7)))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|~r1_xboole_0(X9,X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.50  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.20/0.50  cnf(c_0_24, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.50  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.50  fof(c_0_26, negated_conjecture, (v1_relat_1(esk11_0)&((k10_relat_1(esk11_0,esk10_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk11_0),esk10_0))&(k10_relat_1(esk11_0,esk10_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk11_0),esk10_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.20/0.50  fof(c_0_27, plain, ![X19, X20]:(~r1_xboole_0(k1_tarski(X19),X20)|~r2_hidden(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.20/0.50  fof(c_0_28, plain, ![X18]:r1_xboole_0(X18,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.50  fof(c_0_29, plain, ![X23, X24, X25, X26, X28, X29, X30, X31, X33]:((((r2_hidden(k4_tarski(X26,esk3_4(X23,X24,X25,X26)),X23)|~r2_hidden(X26,X25)|X25!=k10_relat_1(X23,X24)|~v1_relat_1(X23))&(r2_hidden(esk3_4(X23,X24,X25,X26),X24)|~r2_hidden(X26,X25)|X25!=k10_relat_1(X23,X24)|~v1_relat_1(X23)))&(~r2_hidden(k4_tarski(X28,X29),X23)|~r2_hidden(X29,X24)|r2_hidden(X28,X25)|X25!=k10_relat_1(X23,X24)|~v1_relat_1(X23)))&((~r2_hidden(esk4_3(X23,X30,X31),X31)|(~r2_hidden(k4_tarski(esk4_3(X23,X30,X31),X33),X23)|~r2_hidden(X33,X30))|X31=k10_relat_1(X23,X30)|~v1_relat_1(X23))&((r2_hidden(k4_tarski(esk4_3(X23,X30,X31),esk5_3(X23,X30,X31)),X23)|r2_hidden(esk4_3(X23,X30,X31),X31)|X31=k10_relat_1(X23,X30)|~v1_relat_1(X23))&(r2_hidden(esk5_3(X23,X30,X31),X30)|r2_hidden(esk4_3(X23,X30,X31),X31)|X31=k10_relat_1(X23,X30)|~v1_relat_1(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.20/0.50  fof(c_0_30, plain, ![X35, X36, X37, X39, X40, X41, X42, X44]:(((~r2_hidden(X37,X36)|r2_hidden(k4_tarski(esk6_3(X35,X36,X37),X37),X35)|X36!=k2_relat_1(X35))&(~r2_hidden(k4_tarski(X40,X39),X35)|r2_hidden(X39,X36)|X36!=k2_relat_1(X35)))&((~r2_hidden(esk7_2(X41,X42),X42)|~r2_hidden(k4_tarski(X44,esk7_2(X41,X42)),X41)|X42=k2_relat_1(X41))&(r2_hidden(esk7_2(X41,X42),X42)|r2_hidden(k4_tarski(esk8_2(X41,X42),esk7_2(X41,X42)),X41)|X42=k2_relat_1(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.20/0.50  cnf(c_0_31, plain, (r1_xboole_0(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r1_xboole_0(k2_relat_1(X2),X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.50  cnf(c_0_32, negated_conjecture, (k10_relat_1(esk11_0,esk10_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk11_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.50  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.50  cnf(c_0_34, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.50  cnf(c_0_35, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.50  cnf(c_0_36, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.50  cnf(c_0_37, plain, (r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.50  cnf(c_0_38, negated_conjecture, (k10_relat_1(esk11_0,esk10_0)=k1_xboole_0|r1_xboole_0(X1,k10_relat_1(esk11_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.20/0.50  cnf(c_0_39, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.50  cnf(c_0_40, plain, (r2_hidden(esk7_2(X1,X2),X2)|r2_hidden(k4_tarski(esk8_2(X1,X2),esk7_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.50  cnf(c_0_41, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.50  cnf(c_0_42, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_36])).
% 0.20/0.50  cnf(c_0_43, plain, (r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_37])).
% 0.20/0.50  cnf(c_0_44, negated_conjecture, (k10_relat_1(esk11_0,esk10_0)=k1_xboole_0|~r2_hidden(X1,k10_relat_1(esk11_0,esk10_0))), inference(spm,[status(thm)],[c_0_34, c_0_38])).
% 0.20/0.50  cnf(c_0_45, plain, (X1=k1_xboole_0|r2_hidden(esk7_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.20/0.50  cnf(c_0_46, plain, (r2_hidden(esk6_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.50  cnf(c_0_47, negated_conjecture, (k10_relat_1(esk11_0,esk10_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.50  cnf(c_0_48, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.50  cnf(c_0_49, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.50  cnf(c_0_50, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk11_0))|~r2_hidden(X1,esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_33])]), c_0_39])).
% 0.20/0.50  cnf(c_0_51, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.50  cnf(c_0_52, negated_conjecture, (r1_xboole_0(X1,k2_relat_1(esk11_0))|~r2_hidden(esk1_2(X1,k2_relat_1(esk11_0)),esk10_0)), inference(spm,[status(thm)],[c_0_50, c_0_25])).
% 0.20/0.50  cnf(c_0_53, negated_conjecture, (k10_relat_1(esk11_0,esk10_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk11_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.50  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_51, c_0_25])).
% 0.20/0.50  cnf(c_0_55, negated_conjecture, (r1_xboole_0(esk10_0,k2_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_52, c_0_49])).
% 0.20/0.50  cnf(c_0_56, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk11_0),esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_47])])).
% 0.20/0.50  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 58
% 0.20/0.50  # Proof object clause steps            : 36
% 0.20/0.50  # Proof object formula steps           : 22
% 0.20/0.50  # Proof object conjectures             : 14
% 0.20/0.50  # Proof object clause conjectures      : 11
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 16
% 0.20/0.50  # Proof object initial formulas used   : 11
% 0.20/0.50  # Proof object generating inferences   : 15
% 0.20/0.50  # Proof object simplifying inferences  : 13
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 11
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 28
% 0.20/0.50  # Removed in clause preprocessing      : 1
% 0.20/0.50  # Initial clauses in saturation        : 27
% 0.20/0.50  # Processed clauses                    : 1988
% 0.20/0.50  # ...of these trivial                  : 0
% 0.20/0.50  # ...subsumed                          : 1608
% 0.20/0.50  # ...remaining for further processing  : 380
% 0.20/0.50  # Other redundant clauses eliminated   : 5
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 0
% 0.20/0.50  # Backward-rewritten                   : 41
% 0.20/0.50  # Generated clauses                    : 6940
% 0.20/0.50  # ...of the previous two non-trivial   : 6480
% 0.20/0.50  # Contextual simplify-reflections      : 0
% 0.20/0.50  # Paramodulations                      : 6933
% 0.20/0.50  # Factorizations                       : 2
% 0.20/0.50  # Equation resolutions                 : 5
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 308
% 0.20/0.50  #    Positive orientable unit clauses  : 8
% 0.20/0.50  #    Positive unorientable unit clauses: 0
% 0.20/0.50  #    Negative unit clauses             : 2
% 0.20/0.50  #    Non-unit-clauses                  : 298
% 0.20/0.50  # Current number of unprocessed clauses: 4443
% 0.20/0.50  # ...number of literals in the above   : 15533
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 68
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 35014
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 15131
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 1026
% 0.20/0.50  # Unit Clause-clause subsumption calls : 5
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 1
% 0.20/0.50  # BW rewrite match successes           : 1
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 111124
% 0.20/0.50  
% 0.20/0.50  # -------------------------------------------------
% 0.20/0.50  # User time                : 0.149 s
% 0.20/0.50  # System time              : 0.012 s
% 0.20/0.50  # Total time               : 0.161 s
% 0.20/0.50  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
