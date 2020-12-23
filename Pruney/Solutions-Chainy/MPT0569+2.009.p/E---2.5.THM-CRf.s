%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:34 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 156 expanded)
%              Number of clauses        :   37 (  74 expanded)
%              Number of leaves         :   10 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  193 ( 490 expanded)
%              Number of equality atoms :   48 ( 117 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

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

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_10,plain,(
    ! [X28,X29] :
      ( ~ r1_xboole_0(k1_tarski(X28),X29)
      | ~ r2_hidden(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_11,plain,(
    ! [X26] : r1_xboole_0(X26,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_12,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X17,X18] :
      ( ( ~ r2_hidden(esk2_2(X17,X18),X17)
        | ~ r2_hidden(esk2_2(X17,X18),X18)
        | X17 = X18 )
      & ( r2_hidden(esk2_2(X17,X18),X17)
        | r2_hidden(esk2_2(X17,X18),X18)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_15,plain,(
    ! [X20,X21,X23,X24,X25] :
      ( ( r1_xboole_0(X20,X21)
        | r2_hidden(esk3_2(X20,X21),k3_xboole_0(X20,X21)) )
      & ( ~ r2_hidden(X25,k3_xboole_0(X23,X24))
        | ~ r1_xboole_0(X23,X24) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

fof(c_0_19,plain,(
    ! [X60,X61] :
      ( ~ v1_relat_1(X61)
      | k10_relat_1(X61,X60) = k10_relat_1(X61,k3_xboole_0(k2_relat_1(X61),X60)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_22,plain,(
    ! [X32,X33,X34,X35,X37,X38,X39,X40,X42] :
      ( ( r2_hidden(k4_tarski(X35,esk4_4(X32,X33,X34,X35)),X32)
        | ~ r2_hidden(X35,X34)
        | X34 != k10_relat_1(X32,X33)
        | ~ v1_relat_1(X32) )
      & ( r2_hidden(esk4_4(X32,X33,X34,X35),X33)
        | ~ r2_hidden(X35,X34)
        | X34 != k10_relat_1(X32,X33)
        | ~ v1_relat_1(X32) )
      & ( ~ r2_hidden(k4_tarski(X37,X38),X32)
        | ~ r2_hidden(X38,X33)
        | r2_hidden(X37,X34)
        | X34 != k10_relat_1(X32,X33)
        | ~ v1_relat_1(X32) )
      & ( ~ r2_hidden(esk5_3(X32,X39,X40),X40)
        | ~ r2_hidden(k4_tarski(esk5_3(X32,X39,X40),X42),X32)
        | ~ r2_hidden(X42,X39)
        | X40 = k10_relat_1(X32,X39)
        | ~ v1_relat_1(X32) )
      & ( r2_hidden(k4_tarski(esk5_3(X32,X39,X40),esk6_3(X32,X39,X40)),X32)
        | r2_hidden(esk5_3(X32,X39,X40),X40)
        | X40 = k10_relat_1(X32,X39)
        | ~ v1_relat_1(X32) )
      & ( r2_hidden(esk6_3(X32,X39,X40),X39)
        | r2_hidden(esk5_3(X32,X39,X40),X40)
        | X40 = k10_relat_1(X32,X39)
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) )
    & ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_24,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X44,X45,X46,X48,X49,X50,X51,X53] :
      ( ( ~ r2_hidden(X46,X45)
        | r2_hidden(k4_tarski(esk7_3(X44,X45,X46),X46),X44)
        | X45 != k2_relat_1(X44) )
      & ( ~ r2_hidden(k4_tarski(X49,X48),X44)
        | r2_hidden(X48,X45)
        | X45 != k2_relat_1(X44) )
      & ( ~ r2_hidden(esk8_2(X50,X51),X51)
        | ~ r2_hidden(k4_tarski(X53,esk8_2(X50,X51)),X50)
        | X51 = k2_relat_1(X50) )
      & ( r2_hidden(esk8_2(X50,X51),X51)
        | r2_hidden(k4_tarski(esk9_2(X50,X51),esk8_2(X50,X51)),X50)
        | X51 = k2_relat_1(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_29,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( X1 = k10_relat_1(esk12_0,X2)
    | r2_hidden(esk6_3(esk12_0,X2,X1),X2)
    | r2_hidden(esk5_3(esk12_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k10_relat_1(esk12_0,k1_xboole_0)
    | k10_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_27])])).

cnf(c_0_35,negated_conjecture,
    ( k10_relat_1(esk12_0,X1) = k1_xboole_0
    | r2_hidden(esk6_3(esk12_0,X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_31])).

fof(c_0_36,plain,(
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

cnf(c_0_37,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | k10_relat_1(esk12_0,k1_xboole_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k10_relat_1(esk12_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_35])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( r2_hidden(esk7_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk12_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_27])]),c_0_16])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk3_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_46])).

fof(c_0_50,plain,(
    ! [X15,X16] :
      ( ~ r1_xboole_0(X15,X16)
      | r1_xboole_0(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(X1,k2_relat_1(esk12_0))
    | ~ r2_hidden(esk3_2(X1,k2_relat_1(esk12_0)),esk11_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk3_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(esk11_0,k2_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_43])])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 19:00:55 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.51  # AutoSched0-Mode selected heuristic U_____100_C09_12_F1_SE_CS_SP_PS_S5PRR_RG_ND_S04AN
% 0.19/0.51  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.51  #
% 0.19/0.51  # Preprocessing time       : 0.029 s
% 0.19/0.51  # Presaturation interreduction done
% 0.19/0.51  
% 0.19/0.51  # Proof found!
% 0.19/0.51  # SZS status Theorem
% 0.19/0.51  # SZS output start CNFRefutation
% 0.19/0.51  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.19/0.51  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.51  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.19/0.51  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.51  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 0.19/0.51  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 0.19/0.51  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.19/0.51  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.51  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.51  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.51  fof(c_0_10, plain, ![X28, X29]:(~r1_xboole_0(k1_tarski(X28),X29)|~r2_hidden(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.19/0.51  fof(c_0_11, plain, ![X26]:r1_xboole_0(X26,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.51  cnf(c_0_12, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.51  cnf(c_0_13, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.51  fof(c_0_14, plain, ![X17, X18]:((~r2_hidden(esk2_2(X17,X18),X17)|~r2_hidden(esk2_2(X17,X18),X18)|X17=X18)&(r2_hidden(esk2_2(X17,X18),X17)|r2_hidden(esk2_2(X17,X18),X18)|X17=X18)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.19/0.51  fof(c_0_15, plain, ![X20, X21, X23, X24, X25]:((r1_xboole_0(X20,X21)|r2_hidden(esk3_2(X20,X21),k3_xboole_0(X20,X21)))&(~r2_hidden(X25,k3_xboole_0(X23,X24))|~r1_xboole_0(X23,X24))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.51  cnf(c_0_16, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.51  cnf(c_0_17, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.51  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.19/0.51  fof(c_0_19, plain, ![X60, X61]:(~v1_relat_1(X61)|k10_relat_1(X61,X60)=k10_relat_1(X61,k3_xboole_0(k2_relat_1(X61),X60))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.19/0.51  cnf(c_0_20, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.51  cnf(c_0_21, plain, (k1_xboole_0=X1|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.51  fof(c_0_22, plain, ![X32, X33, X34, X35, X37, X38, X39, X40, X42]:((((r2_hidden(k4_tarski(X35,esk4_4(X32,X33,X34,X35)),X32)|~r2_hidden(X35,X34)|X34!=k10_relat_1(X32,X33)|~v1_relat_1(X32))&(r2_hidden(esk4_4(X32,X33,X34,X35),X33)|~r2_hidden(X35,X34)|X34!=k10_relat_1(X32,X33)|~v1_relat_1(X32)))&(~r2_hidden(k4_tarski(X37,X38),X32)|~r2_hidden(X38,X33)|r2_hidden(X37,X34)|X34!=k10_relat_1(X32,X33)|~v1_relat_1(X32)))&((~r2_hidden(esk5_3(X32,X39,X40),X40)|(~r2_hidden(k4_tarski(esk5_3(X32,X39,X40),X42),X32)|~r2_hidden(X42,X39))|X40=k10_relat_1(X32,X39)|~v1_relat_1(X32))&((r2_hidden(k4_tarski(esk5_3(X32,X39,X40),esk6_3(X32,X39,X40)),X32)|r2_hidden(esk5_3(X32,X39,X40),X40)|X40=k10_relat_1(X32,X39)|~v1_relat_1(X32))&(r2_hidden(esk6_3(X32,X39,X40),X39)|r2_hidden(esk5_3(X32,X39,X40),X40)|X40=k10_relat_1(X32,X39)|~v1_relat_1(X32))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.19/0.51  fof(c_0_23, negated_conjecture, (v1_relat_1(esk12_0)&((k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0))&(k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.19/0.51  cnf(c_0_24, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.51  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.51  cnf(c_0_26, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.51  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.51  fof(c_0_28, plain, ![X44, X45, X46, X48, X49, X50, X51, X53]:(((~r2_hidden(X46,X45)|r2_hidden(k4_tarski(esk7_3(X44,X45,X46),X46),X44)|X45!=k2_relat_1(X44))&(~r2_hidden(k4_tarski(X49,X48),X44)|r2_hidden(X48,X45)|X45!=k2_relat_1(X44)))&((~r2_hidden(esk8_2(X50,X51),X51)|~r2_hidden(k4_tarski(X53,esk8_2(X50,X51)),X50)|X51=k2_relat_1(X50))&(r2_hidden(esk8_2(X50,X51),X51)|r2_hidden(k4_tarski(esk9_2(X50,X51),esk8_2(X50,X51)),X50)|X51=k2_relat_1(X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.51  cnf(c_0_29, plain, (k10_relat_1(X1,k1_xboole_0)=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.51  cnf(c_0_30, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.51  cnf(c_0_31, negated_conjecture, (X1=k10_relat_1(esk12_0,X2)|r2_hidden(esk6_3(esk12_0,X2,X1),X2)|r2_hidden(esk5_3(esk12_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.51  cnf(c_0_32, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.51  cnf(c_0_33, plain, (r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.51  cnf(c_0_34, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k10_relat_1(esk12_0,k1_xboole_0)|k10_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_27])])).
% 0.19/0.51  cnf(c_0_35, negated_conjecture, (k10_relat_1(esk12_0,X1)=k1_xboole_0|r2_hidden(esk6_3(esk12_0,X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_16, c_0_31])).
% 0.19/0.51  fof(c_0_36, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7))&(r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k3_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k3_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))&(r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.51  cnf(c_0_37, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.51  cnf(c_0_38, plain, (r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_33])).
% 0.19/0.51  cnf(c_0_39, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|k10_relat_1(esk12_0,k1_xboole_0)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_34])).
% 0.19/0.51  cnf(c_0_40, negated_conjecture, (k10_relat_1(esk12_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_35])).
% 0.19/0.51  cnf(c_0_41, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.51  cnf(c_0_42, plain, (r2_hidden(esk7_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.51  cnf(c_0_43, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40])])).
% 0.19/0.51  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_41])).
% 0.19/0.51  cnf(c_0_45, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.51  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.51  cnf(c_0_47, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk12_0))|~r2_hidden(X1,esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_27])]), c_0_16])).
% 0.19/0.51  cnf(c_0_48, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk3_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.51  cnf(c_0_49, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_46])).
% 0.19/0.51  fof(c_0_50, plain, ![X15, X16]:(~r1_xboole_0(X15,X16)|r1_xboole_0(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.51  cnf(c_0_51, negated_conjecture, (r1_xboole_0(X1,k2_relat_1(esk12_0))|~r2_hidden(esk3_2(X1,k2_relat_1(esk12_0)),esk11_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.51  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk3_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_49, c_0_45])).
% 0.19/0.51  cnf(c_0_53, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.51  cnf(c_0_54, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.51  cnf(c_0_55, negated_conjecture, (r1_xboole_0(esk11_0,k2_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.51  cnf(c_0_56, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_43])])).
% 0.19/0.51  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), ['proof']).
% 0.19/0.51  # SZS output end CNFRefutation
% 0.19/0.51  # Proof object total steps             : 58
% 0.19/0.51  # Proof object clause steps            : 37
% 0.19/0.51  # Proof object formula steps           : 21
% 0.19/0.51  # Proof object conjectures             : 17
% 0.19/0.51  # Proof object clause conjectures      : 14
% 0.19/0.51  # Proof object formula conjectures     : 3
% 0.19/0.51  # Proof object initial clauses used    : 15
% 0.19/0.51  # Proof object initial formulas used   : 10
% 0.19/0.51  # Proof object generating inferences   : 16
% 0.19/0.51  # Proof object simplifying inferences  : 14
% 0.19/0.51  # Training examples: 0 positive, 0 negative
% 0.19/0.51  # Parsed axioms                        : 13
% 0.19/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.51  # Initial clauses                      : 33
% 0.19/0.51  # Removed in clause preprocessing      : 0
% 0.19/0.51  # Initial clauses in saturation        : 33
% 0.19/0.51  # Processed clauses                    : 1979
% 0.19/0.51  # ...of these trivial                  : 7
% 0.19/0.51  # ...subsumed                          : 1553
% 0.19/0.51  # ...remaining for further processing  : 419
% 0.19/0.51  # Other redundant clauses eliminated   : 8
% 0.19/0.51  # Clauses deleted for lack of memory   : 0
% 0.19/0.51  # Backward-subsumed                    : 4
% 0.19/0.51  # Backward-rewritten                   : 31
% 0.19/0.51  # Generated clauses                    : 9855
% 0.19/0.51  # ...of the previous two non-trivial   : 8632
% 0.19/0.51  # Contextual simplify-reflections      : 0
% 0.19/0.51  # Paramodulations                      : 9802
% 0.19/0.51  # Factorizations                       : 45
% 0.19/0.51  # Equation resolutions                 : 8
% 0.19/0.51  # Propositional unsat checks           : 0
% 0.19/0.51  #    Propositional check models        : 0
% 0.19/0.51  #    Propositional check unsatisfiable : 0
% 0.19/0.51  #    Propositional clauses             : 0
% 0.19/0.51  #    Propositional clauses after purity: 0
% 0.19/0.51  #    Propositional unsat core size     : 0
% 0.19/0.51  #    Propositional preprocessing time  : 0.000
% 0.19/0.51  #    Propositional encoding time       : 0.000
% 0.19/0.51  #    Propositional solver time         : 0.000
% 0.19/0.51  #    Success case prop preproc time    : 0.000
% 0.19/0.51  #    Success case prop encoding time   : 0.000
% 0.19/0.51  #    Success case prop solver time     : 0.000
% 0.19/0.51  # Current number of processed clauses  : 344
% 0.19/0.51  #    Positive orientable unit clauses  : 11
% 0.19/0.51  #    Positive unorientable unit clauses: 1
% 0.19/0.51  #    Negative unit clauses             : 2
% 0.19/0.51  #    Non-unit-clauses                  : 330
% 0.19/0.51  # Current number of unprocessed clauses: 6662
% 0.19/0.51  # ...number of literals in the above   : 19949
% 0.19/0.51  # Current number of archived formulas  : 0
% 0.19/0.51  # Current number of archived clauses   : 67
% 0.19/0.51  # Clause-clause subsumption calls (NU) : 40022
% 0.19/0.51  # Rec. Clause-clause subsumption calls : 27784
% 0.19/0.51  # Non-unit clause-clause subsumptions  : 1172
% 0.19/0.51  # Unit Clause-clause subsumption calls : 211
% 0.19/0.51  # Rewrite failures with RHS unbound    : 0
% 0.19/0.51  # BW rewrite match attempts            : 16
% 0.19/0.51  # BW rewrite match successes           : 9
% 0.19/0.51  # Condensation attempts                : 0
% 0.19/0.51  # Condensation successes               : 0
% 0.19/0.51  # Termbank termtop insertions          : 142558
% 0.19/0.51  
% 0.19/0.51  # -------------------------------------------------
% 0.19/0.51  # User time                : 0.173 s
% 0.19/0.51  # System time              : 0.008 s
% 0.19/0.51  # Total time               : 0.181 s
% 0.19/0.51  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
