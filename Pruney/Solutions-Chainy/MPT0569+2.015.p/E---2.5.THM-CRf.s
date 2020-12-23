%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 137 expanded)
%              Number of clauses        :   34 (  63 expanded)
%              Number of leaves         :   10 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  193 ( 434 expanded)
%              Number of equality atoms :   48 ( 112 expanded)
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

fof(t168_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,X1) = k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

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
    ! [X55,X56] :
      ( ~ v1_relat_1(X56)
      | k10_relat_1(X56,X55) = k10_relat_1(X56,k3_xboole_0(k2_relat_1(X56),X55)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

fof(c_0_16,plain,(
    ! [X50,X51,X52,X54] :
      ( ( r2_hidden(esk10_3(X50,X51,X52),k2_relat_1(X52))
        | ~ r2_hidden(X50,k10_relat_1(X52,X51))
        | ~ v1_relat_1(X52) )
      & ( r2_hidden(k4_tarski(X50,esk10_3(X50,X51,X52)),X52)
        | ~ r2_hidden(X50,k10_relat_1(X52,X51))
        | ~ v1_relat_1(X52) )
      & ( r2_hidden(esk10_3(X50,X51,X52),X51)
        | ~ r2_hidden(X50,k10_relat_1(X52,X51))
        | ~ v1_relat_1(X52) )
      & ( ~ r2_hidden(X54,k2_relat_1(X52))
        | ~ r2_hidden(k4_tarski(X50,X54),X52)
        | ~ r2_hidden(X54,X51)
        | r2_hidden(X50,k10_relat_1(X52,X51))
        | ~ v1_relat_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_17,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) )
    & ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_20,plain,(
    ! [X23] : k3_xboole_0(X23,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_21,plain,(
    ! [X24] : r1_xboole_0(X24,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_22,plain,
    ( r2_hidden(esk10_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X27,X28,X29,X30,X32,X33,X34,X35,X37] :
      ( ( r2_hidden(k4_tarski(X30,esk4_4(X27,X28,X29,X30)),X27)
        | ~ r2_hidden(X30,X29)
        | X29 != k10_relat_1(X27,X28)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(esk4_4(X27,X28,X29,X30),X28)
        | ~ r2_hidden(X30,X29)
        | X29 != k10_relat_1(X27,X28)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(X32,X33),X27)
        | ~ r2_hidden(X33,X28)
        | r2_hidden(X32,X29)
        | X29 != k10_relat_1(X27,X28)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(esk5_3(X27,X34,X35),X35)
        | ~ r2_hidden(k4_tarski(esk5_3(X27,X34,X35),X37),X27)
        | ~ r2_hidden(X37,X34)
        | X35 = k10_relat_1(X27,X34)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk5_3(X27,X34,X35),esk6_3(X27,X34,X35)),X27)
        | r2_hidden(esk5_3(X27,X34,X35),X35)
        | X35 = k10_relat_1(X27,X34)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(esk6_3(X27,X34,X35),X34)
        | r2_hidden(esk5_3(X27,X34,X35),X35)
        | X35 = k10_relat_1(X27,X34)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_24,plain,(
    ! [X39,X40,X41,X43,X44,X45,X46,X48] :
      ( ( ~ r2_hidden(X41,X40)
        | r2_hidden(k4_tarski(esk7_3(X39,X40,X41),X41),X39)
        | X40 != k2_relat_1(X39) )
      & ( ~ r2_hidden(k4_tarski(X44,X43),X39)
        | r2_hidden(X43,X40)
        | X40 != k2_relat_1(X39) )
      & ( ~ r2_hidden(esk8_2(X45,X46),X46)
        | ~ r2_hidden(k4_tarski(X48,esk8_2(X45,X46)),X45)
        | X46 = k2_relat_1(X45) )
      & ( r2_hidden(esk8_2(X45,X46),X46)
        | r2_hidden(k4_tarski(esk9_2(X45,X46),esk8_2(X45,X46)),X45)
        | X46 = k2_relat_1(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_25,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(esk10_3(esk3_1(k10_relat_1(X1,X2)),X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_14])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k10_relat_1(esk12_0,k1_xboole_0)
    | k10_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_28]),c_0_29])])).

cnf(c_0_35,negated_conjecture,
    ( k10_relat_1(esk12_0,X1) = k1_xboole_0
    | r2_hidden(esk10_3(esk3_1(k10_relat_1(esk12_0,X1)),X1,esk12_0),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

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
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | k10_relat_1(esk12_0,k1_xboole_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k10_relat_1(esk12_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
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
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk12_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_27])]),c_0_34])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk12_0),X1)
    | ~ r2_hidden(esk2_2(k2_relat_1(esk12_0),X1),esk11_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_43])])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:41:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic U_____100_C09_12_F1_SE_CS_SP_PS_S5PRR_RG_ND_S04AN
% 0.20/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.029 s
% 0.20/0.45  # Presaturation interreduction done
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.45  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.45  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 0.20/0.45  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.20/0.45  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.20/0.45  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.45  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.45  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 0.20/0.45  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.20/0.45  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.45  fof(c_0_10, plain, ![X15, X16, X18, X19, X20]:((r1_xboole_0(X15,X16)|r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)))&(~r2_hidden(X20,k3_xboole_0(X18,X19))|~r1_xboole_0(X18,X19))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.45  fof(c_0_11, plain, ![X21]:(X21=k1_xboole_0|r2_hidden(esk3_1(X21),X21)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.45  fof(c_0_12, plain, ![X55, X56]:(~v1_relat_1(X56)|k10_relat_1(X56,X55)=k10_relat_1(X56,k3_xboole_0(k2_relat_1(X56),X55))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.20/0.45  cnf(c_0_13, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.45  cnf(c_0_14, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.45  fof(c_0_15, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.20/0.45  fof(c_0_16, plain, ![X50, X51, X52, X54]:((((r2_hidden(esk10_3(X50,X51,X52),k2_relat_1(X52))|~r2_hidden(X50,k10_relat_1(X52,X51))|~v1_relat_1(X52))&(r2_hidden(k4_tarski(X50,esk10_3(X50,X51,X52)),X52)|~r2_hidden(X50,k10_relat_1(X52,X51))|~v1_relat_1(X52)))&(r2_hidden(esk10_3(X50,X51,X52),X51)|~r2_hidden(X50,k10_relat_1(X52,X51))|~v1_relat_1(X52)))&(~r2_hidden(X54,k2_relat_1(X52))|~r2_hidden(k4_tarski(X50,X54),X52)|~r2_hidden(X54,X51)|r2_hidden(X50,k10_relat_1(X52,X51))|~v1_relat_1(X52))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.20/0.45  cnf(c_0_17, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.45  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.45  fof(c_0_19, negated_conjecture, (v1_relat_1(esk12_0)&((k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0))&(k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.20/0.45  fof(c_0_20, plain, ![X23]:k3_xboole_0(X23,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.45  fof(c_0_21, plain, ![X24]:r1_xboole_0(X24,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.45  cnf(c_0_22, plain, (r2_hidden(esk10_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.45  fof(c_0_23, plain, ![X27, X28, X29, X30, X32, X33, X34, X35, X37]:((((r2_hidden(k4_tarski(X30,esk4_4(X27,X28,X29,X30)),X27)|~r2_hidden(X30,X29)|X29!=k10_relat_1(X27,X28)|~v1_relat_1(X27))&(r2_hidden(esk4_4(X27,X28,X29,X30),X28)|~r2_hidden(X30,X29)|X29!=k10_relat_1(X27,X28)|~v1_relat_1(X27)))&(~r2_hidden(k4_tarski(X32,X33),X27)|~r2_hidden(X33,X28)|r2_hidden(X32,X29)|X29!=k10_relat_1(X27,X28)|~v1_relat_1(X27)))&((~r2_hidden(esk5_3(X27,X34,X35),X35)|(~r2_hidden(k4_tarski(esk5_3(X27,X34,X35),X37),X27)|~r2_hidden(X37,X34))|X35=k10_relat_1(X27,X34)|~v1_relat_1(X27))&((r2_hidden(k4_tarski(esk5_3(X27,X34,X35),esk6_3(X27,X34,X35)),X27)|r2_hidden(esk5_3(X27,X34,X35),X35)|X35=k10_relat_1(X27,X34)|~v1_relat_1(X27))&(r2_hidden(esk6_3(X27,X34,X35),X34)|r2_hidden(esk5_3(X27,X34,X35),X35)|X35=k10_relat_1(X27,X34)|~v1_relat_1(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.20/0.45  fof(c_0_24, plain, ![X39, X40, X41, X43, X44, X45, X46, X48]:(((~r2_hidden(X41,X40)|r2_hidden(k4_tarski(esk7_3(X39,X40,X41),X41),X39)|X40!=k2_relat_1(X39))&(~r2_hidden(k4_tarski(X44,X43),X39)|r2_hidden(X43,X40)|X40!=k2_relat_1(X39)))&((~r2_hidden(esk8_2(X45,X46),X46)|~r2_hidden(k4_tarski(X48,esk8_2(X45,X46)),X45)|X46=k2_relat_1(X45))&(r2_hidden(esk8_2(X45,X46),X46)|r2_hidden(k4_tarski(esk9_2(X45,X46),esk8_2(X45,X46)),X45)|X46=k2_relat_1(X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.20/0.45  cnf(c_0_25, plain, (k10_relat_1(X1,k1_xboole_0)=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.45  cnf(c_0_26, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_28, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_29, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.45  cnf(c_0_30, plain, (k10_relat_1(X1,X2)=k1_xboole_0|r2_hidden(esk10_3(esk3_1(k10_relat_1(X1,X2)),X2,X1),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_14])).
% 0.20/0.45  cnf(c_0_31, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.45  cnf(c_0_32, plain, (r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.45  cnf(c_0_33, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k10_relat_1(esk12_0,k1_xboole_0)|k10_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.20/0.45  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_28]), c_0_29])])).
% 0.20/0.45  cnf(c_0_35, negated_conjecture, (k10_relat_1(esk12_0,X1)=k1_xboole_0|r2_hidden(esk10_3(esk3_1(k10_relat_1(esk12_0,X1)),X1,esk12_0),X1)), inference(spm,[status(thm)],[c_0_30, c_0_27])).
% 0.20/0.45  fof(c_0_36, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7))&(r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k3_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k3_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))&(r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.45  cnf(c_0_37, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_31])).
% 0.20/0.45  cnf(c_0_38, plain, (r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_32])).
% 0.20/0.45  cnf(c_0_39, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|k10_relat_1(esk12_0,k1_xboole_0)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_33])).
% 0.20/0.45  cnf(c_0_40, negated_conjecture, (k10_relat_1(esk12_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.45  cnf(c_0_41, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.45  cnf(c_0_42, plain, (r2_hidden(esk7_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.45  cnf(c_0_43, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40])])).
% 0.20/0.45  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_41])).
% 0.20/0.45  cnf(c_0_45, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.45  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.45  cnf(c_0_47, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk12_0))|~r2_hidden(X1,esk11_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_27])]), c_0_34])).
% 0.20/0.45  cnf(c_0_48, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.45  cnf(c_0_49, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_46])).
% 0.20/0.45  cnf(c_0_50, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_51, negated_conjecture, (r1_xboole_0(k2_relat_1(esk12_0),X1)|~r2_hidden(esk2_2(k2_relat_1(esk12_0),X1),esk11_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.45  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_49, c_0_45])).
% 0.20/0.45  cnf(c_0_53, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_43])])).
% 0.20/0.45  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 55
% 0.20/0.45  # Proof object clause steps            : 34
% 0.20/0.45  # Proof object formula steps           : 21
% 0.20/0.45  # Proof object conjectures             : 15
% 0.20/0.45  # Proof object clause conjectures      : 12
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 14
% 0.20/0.45  # Proof object initial formulas used   : 10
% 0.20/0.45  # Proof object generating inferences   : 14
% 0.20/0.45  # Proof object simplifying inferences  : 16
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 11
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 30
% 0.20/0.45  # Removed in clause preprocessing      : 0
% 0.20/0.45  # Initial clauses in saturation        : 30
% 0.20/0.45  # Processed clauses                    : 1210
% 0.20/0.45  # ...of these trivial                  : 2
% 0.20/0.45  # ...subsumed                          : 956
% 0.20/0.45  # ...remaining for further processing  : 252
% 0.20/0.45  # Other redundant clauses eliminated   : 8
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 2
% 0.20/0.45  # Backward-rewritten                   : 9
% 0.20/0.45  # Generated clauses                    : 4445
% 0.20/0.45  # ...of the previous two non-trivial   : 3626
% 0.20/0.45  # Contextual simplify-reflections      : 0
% 0.20/0.45  # Paramodulations                      : 4430
% 0.20/0.45  # Factorizations                       : 7
% 0.20/0.45  # Equation resolutions                 : 8
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 204
% 0.20/0.45  #    Positive orientable unit clauses  : 12
% 0.20/0.45  #    Positive unorientable unit clauses: 0
% 0.20/0.45  #    Negative unit clauses             : 2
% 0.20/0.45  #    Non-unit-clauses                  : 190
% 0.20/0.45  # Current number of unprocessed clauses: 2461
% 0.20/0.45  # ...number of literals in the above   : 7965
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 40
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 11702
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 8136
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 698
% 0.20/0.45  # Unit Clause-clause subsumption calls : 21
% 0.20/0.45  # Rewrite failures with RHS unbound    : 0
% 0.20/0.45  # BW rewrite match attempts            : 5
% 0.20/0.45  # BW rewrite match successes           : 5
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 67417
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.101 s
% 0.20/0.45  # System time              : 0.010 s
% 0.20/0.45  # Total time               : 0.112 s
% 0.20/0.45  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
