%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:33 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 274 expanded)
%              Number of clauses        :   46 ( 132 expanded)
%              Number of leaves         :    9 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  213 (1007 expanded)
%              Number of equality atoms :   55 ( 261 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X17,X18,X20,X21,X22] :
      ( ( r1_xboole_0(X17,X18)
        | r2_hidden(esk2_2(X17,X18),k3_xboole_0(X17,X18)) )
      & ( ~ r2_hidden(X22,k3_xboole_0(X20,X21))
        | ~ r1_xboole_0(X20,X21) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & ( k10_relat_1(esk10_0,esk9_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk10_0),esk9_0) )
    & ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X24,X25] :
      ( ~ r1_xboole_0(k1_tarski(X24),X25)
      | ~ r2_hidden(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_24,plain,(
    ! [X23] : r1_xboole_0(X23,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_25,plain,(
    ! [X28,X29,X30,X31,X33,X34,X35,X36,X38] :
      ( ( r2_hidden(k4_tarski(X31,esk3_4(X28,X29,X30,X31)),X28)
        | ~ r2_hidden(X31,X30)
        | X30 != k10_relat_1(X28,X29)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(esk3_4(X28,X29,X30,X31),X29)
        | ~ r2_hidden(X31,X30)
        | X30 != k10_relat_1(X28,X29)
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(X33,X34),X28)
        | ~ r2_hidden(X34,X29)
        | r2_hidden(X33,X30)
        | X30 != k10_relat_1(X28,X29)
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(esk4_3(X28,X35,X36),X36)
        | ~ r2_hidden(k4_tarski(esk4_3(X28,X35,X36),X38),X28)
        | ~ r2_hidden(X38,X35)
        | X36 = k10_relat_1(X28,X35)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(k4_tarski(esk4_3(X28,X35,X36),esk5_3(X28,X35,X36)),X28)
        | r2_hidden(esk4_3(X28,X35,X36),X36)
        | X36 = k10_relat_1(X28,X35)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(esk5_3(X28,X35,X36),X35)
        | r2_hidden(esk4_3(X28,X35,X36),X36)
        | X36 = k10_relat_1(X28,X35)
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_26,plain,(
    ! [X51,X52] :
      ( ~ v1_relat_1(X52)
      | k10_relat_1(X52,X51) = k10_relat_1(X52,k3_xboole_0(k2_relat_1(X52),X51)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

fof(c_0_27,plain,(
    ! [X15,X16] :
      ( ( ~ r1_xboole_0(X15,X16)
        | k3_xboole_0(X15,X16) = k1_xboole_0 )
      & ( k3_xboole_0(X15,X16) != k1_xboole_0
        | r1_xboole_0(X15,X16) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_28,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | ~ r2_hidden(X1,k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_31,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X40,X41,X42,X44,X45,X46,X47,X49] :
      ( ( ~ r2_hidden(X42,X41)
        | r2_hidden(k4_tarski(esk6_3(X40,X41,X42),X42),X40)
        | X41 != k2_relat_1(X40) )
      & ( ~ r2_hidden(k4_tarski(X45,X44),X40)
        | r2_hidden(X44,X41)
        | X41 != k2_relat_1(X40) )
      & ( ~ r2_hidden(esk7_2(X46,X47),X47)
        | ~ r2_hidden(k4_tarski(X49,esk7_2(X46,X47)),X46)
        | X47 = k2_relat_1(X46) )
      & ( r2_hidden(esk7_2(X46,X47),X47)
        | r2_hidden(k4_tarski(esk8_2(X46,X47),esk7_2(X46,X47)),X46)
        | X47 = k2_relat_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_34,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk10_0),X1)
    | ~ r2_hidden(esk2_2(k2_relat_1(esk10_0),X1),esk9_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | r2_hidden(esk2_2(X1,k3_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_30])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk8_2(X1,X2),esk7_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r2_hidden(esk3_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk10_0),k3_xboole_0(X1,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk7_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X4,k10_relat_1(X1,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k10_relat_1(esk10_0,k3_xboole_0(X1,esk9_0)) = k10_relat_1(esk10_0,k1_xboole_0)
    | k10_relat_1(esk10_0,esk9_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_48,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k10_relat_1(esk10_0,k1_xboole_0)
    | k10_relat_1(esk10_0,esk9_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_19]),c_0_44])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_51,plain,
    ( r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_52,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk9_0)
    | ~ r2_hidden(X2,k10_relat_1(esk10_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_44])])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk7_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_45,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | k10_relat_1(esk10_0,k1_xboole_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_58,plain,
    ( r2_hidden(esk6_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_44])]),c_0_39])).

cnf(c_0_61,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk10_0),X1)
    | ~ r2_hidden(esk2_2(k2_relat_1(esk10_0),X1),esk9_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_59])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_30]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic U_____100_C09_12_F1_SE_CS_SP_PS_S5PRR_RG_ND_S04AN
% 0.20/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.028 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.40  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.40  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 0.20/0.40  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.20/0.40  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.40  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.20/0.40  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 0.20/0.40  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.40  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.20/0.40  fof(c_0_9, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7))&(r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k3_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k3_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))&(r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.40  fof(c_0_10, plain, ![X17, X18, X20, X21, X22]:((r1_xboole_0(X17,X18)|r2_hidden(esk2_2(X17,X18),k3_xboole_0(X17,X18)))&(~r2_hidden(X22,k3_xboole_0(X20,X21))|~r1_xboole_0(X20,X21))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.40  cnf(c_0_11, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.20/0.40  cnf(c_0_13, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_14, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_11])).
% 0.20/0.40  fof(c_0_15, negated_conjecture, (v1_relat_1(esk10_0)&((k10_relat_1(esk10_0,esk9_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk10_0),esk9_0))&(k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk10_0),esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.20/0.40  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_18, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.40  cnf(c_0_19, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_21, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_22, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.20/0.40  fof(c_0_23, plain, ![X24, X25]:(~r1_xboole_0(k1_tarski(X24),X25)|~r2_hidden(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.20/0.40  fof(c_0_24, plain, ![X23]:r1_xboole_0(X23,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.40  fof(c_0_25, plain, ![X28, X29, X30, X31, X33, X34, X35, X36, X38]:((((r2_hidden(k4_tarski(X31,esk3_4(X28,X29,X30,X31)),X28)|~r2_hidden(X31,X30)|X30!=k10_relat_1(X28,X29)|~v1_relat_1(X28))&(r2_hidden(esk3_4(X28,X29,X30,X31),X29)|~r2_hidden(X31,X30)|X30!=k10_relat_1(X28,X29)|~v1_relat_1(X28)))&(~r2_hidden(k4_tarski(X33,X34),X28)|~r2_hidden(X34,X29)|r2_hidden(X33,X30)|X30!=k10_relat_1(X28,X29)|~v1_relat_1(X28)))&((~r2_hidden(esk4_3(X28,X35,X36),X36)|(~r2_hidden(k4_tarski(esk4_3(X28,X35,X36),X38),X28)|~r2_hidden(X38,X35))|X36=k10_relat_1(X28,X35)|~v1_relat_1(X28))&((r2_hidden(k4_tarski(esk4_3(X28,X35,X36),esk5_3(X28,X35,X36)),X28)|r2_hidden(esk4_3(X28,X35,X36),X36)|X36=k10_relat_1(X28,X35)|~v1_relat_1(X28))&(r2_hidden(esk5_3(X28,X35,X36),X35)|r2_hidden(esk4_3(X28,X35,X36),X36)|X36=k10_relat_1(X28,X35)|~v1_relat_1(X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.20/0.40  fof(c_0_26, plain, ![X51, X52]:(~v1_relat_1(X52)|k10_relat_1(X52,X51)=k10_relat_1(X52,k3_xboole_0(k2_relat_1(X52),X51))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.20/0.40  fof(c_0_27, plain, ![X15, X16]:((~r1_xboole_0(X15,X16)|k3_xboole_0(X15,X16)=k1_xboole_0)&(k3_xboole_0(X15,X16)!=k1_xboole_0|r1_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|~r2_hidden(X1,k2_relat_1(esk10_0))|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.40  cnf(c_0_29, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.40  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.20/0.40  cnf(c_0_31, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.40  cnf(c_0_32, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  fof(c_0_33, plain, ![X40, X41, X42, X44, X45, X46, X47, X49]:(((~r2_hidden(X42,X41)|r2_hidden(k4_tarski(esk6_3(X40,X41,X42),X42),X40)|X41!=k2_relat_1(X40))&(~r2_hidden(k4_tarski(X45,X44),X40)|r2_hidden(X44,X41)|X41!=k2_relat_1(X40)))&((~r2_hidden(esk7_2(X46,X47),X47)|~r2_hidden(k4_tarski(X49,esk7_2(X46,X47)),X46)|X47=k2_relat_1(X46))&(r2_hidden(esk7_2(X46,X47),X47)|r2_hidden(k4_tarski(esk8_2(X46,X47),esk7_2(X46,X47)),X46)|X47=k2_relat_1(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.20/0.40  cnf(c_0_34, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_35, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_37, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk10_0),X1)|~r2_hidden(esk2_2(k2_relat_1(esk10_0),X1),esk9_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.40  cnf(c_0_38, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|r2_hidden(esk2_2(X1,k3_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_22, c_0_30])).
% 0.20/0.40  cnf(c_0_39, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.40  cnf(c_0_40, plain, (r2_hidden(esk7_2(X1,X2),X2)|r2_hidden(k4_tarski(esk8_2(X1,X2),esk7_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.40  cnf(c_0_41, plain, (r2_hidden(esk3_4(X1,X2,k10_relat_1(X1,X2),X3),X2)|~v1_relat_1(X1)|~r2_hidden(X3,k10_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_34])).
% 0.20/0.40  cnf(c_0_42, plain, (k10_relat_1(X1,k1_xboole_0)=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk10_0),k3_xboole_0(X1,esk9_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_45, plain, (X1=k2_relat_1(k1_xboole_0)|r2_hidden(esk7_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.40  cnf(c_0_46, plain, (~v1_relat_1(X1)|~r1_xboole_0(X2,X3)|~r2_hidden(X4,k10_relat_1(X1,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_13, c_0_41])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (k10_relat_1(esk10_0,k3_xboole_0(X1,esk9_0))=k10_relat_1(esk10_0,k1_xboole_0)|k10_relat_1(esk10_0,esk9_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.20/0.40  cnf(c_0_48, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_45])).
% 0.20/0.40  cnf(c_0_49, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k10_relat_1(esk10_0,k1_xboole_0)|k10_relat_1(esk10_0,esk9_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_19]), c_0_44])])).
% 0.20/0.40  cnf(c_0_50, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_51, plain, (r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.40  cnf(c_0_52, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|~r1_xboole_0(X1,esk9_0)|~r2_hidden(X2,k10_relat_1(esk10_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_44])])).
% 0.20/0.40  cnf(c_0_53, plain, (X1=k1_xboole_0|r2_hidden(esk7_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_45, c_0_48])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|k10_relat_1(esk10_0,k1_xboole_0)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_49])).
% 0.20/0.40  cnf(c_0_55, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_50])).
% 0.20/0.40  cnf(c_0_56, plain, (r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_51])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|~r1_xboole_0(X1,esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.20/0.40  cnf(c_0_58, plain, (r2_hidden(esk6_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_19])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk10_0))|~r2_hidden(X1,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_44])]), c_0_39])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_62, negated_conjecture, (r1_xboole_0(k2_relat_1(esk10_0),X1)|~r2_hidden(esk2_2(k2_relat_1(esk10_0),X1),esk9_0)), inference(spm,[status(thm)],[c_0_60, c_0_29])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk10_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_59])])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_30]), c_0_63]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 65
% 0.20/0.40  # Proof object clause steps            : 46
% 0.20/0.40  # Proof object formula steps           : 19
% 0.20/0.40  # Proof object conjectures             : 19
% 0.20/0.40  # Proof object clause conjectures      : 16
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 16
% 0.20/0.40  # Proof object initial formulas used   : 9
% 0.20/0.40  # Proof object generating inferences   : 22
% 0.20/0.40  # Proof object simplifying inferences  : 20
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 11
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 28
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 28
% 0.20/0.40  # Processed clauses                    : 581
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 387
% 0.20/0.40  # ...remaining for further processing  : 194
% 0.20/0.40  # Other redundant clauses eliminated   : 8
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 4
% 0.20/0.40  # Backward-rewritten                   : 36
% 0.20/0.40  # Generated clauses                    : 1667
% 0.20/0.40  # ...of the previous two non-trivial   : 1436
% 0.20/0.40  # Contextual simplify-reflections      : 1
% 0.20/0.40  # Paramodulations                      : 1652
% 0.20/0.40  # Factorizations                       : 7
% 0.20/0.40  # Equation resolutions                 : 8
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 118
% 0.20/0.40  #    Positive orientable unit clauses  : 11
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 2
% 0.20/0.40  #    Non-unit-clauses                  : 105
% 0.20/0.40  # Current number of unprocessed clauses: 862
% 0.20/0.40  # ...number of literals in the above   : 2572
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 68
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 2185
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 1510
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 259
% 0.20/0.40  # Unit Clause-clause subsumption calls : 37
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 16
% 0.20/0.40  # BW rewrite match successes           : 4
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 23551
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.060 s
% 0.20/0.40  # System time              : 0.005 s
% 0.20/0.40  # Total time               : 0.065 s
% 0.20/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
