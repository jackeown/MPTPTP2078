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

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 292 expanded)
%              Number of clauses        :   50 ( 142 expanded)
%              Number of leaves         :   10 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  224 (1026 expanded)
%              Number of equality atoms :   57 ( 255 expanded)
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

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

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

fof(c_0_10,plain,(
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

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

fof(c_0_12,plain,(
    ! [X19,X20,X22,X23,X24] :
      ( ( r1_xboole_0(X19,X20)
        | r2_hidden(esk2_2(X19,X20),k3_xboole_0(X19,X20)) )
      & ( ~ r2_hidden(X24,k3_xboole_0(X22,X23))
        | ~ r1_xboole_0(X22,X23) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X17,X18] :
      ( ~ r1_xboole_0(X17,X18)
      | r1_xboole_0(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & ( k10_relat_1(esk10_0,esk9_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk10_0),esk9_0) )
    & ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | r1_xboole_0(esk9_0,k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | ~ r2_hidden(X1,k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

fof(c_0_30,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_xboole_0(k2_tarski(X26,X27),X28)
      | ~ r2_hidden(X26,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

fof(c_0_31,plain,(
    ! [X25] : r1_xboole_0(X25,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_32,plain,(
    ! [X31,X32,X33,X34,X36,X37,X38,X39,X41] :
      ( ( r2_hidden(k4_tarski(X34,esk3_4(X31,X32,X33,X34)),X31)
        | ~ r2_hidden(X34,X33)
        | X33 != k10_relat_1(X31,X32)
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(esk3_4(X31,X32,X33,X34),X32)
        | ~ r2_hidden(X34,X33)
        | X33 != k10_relat_1(X31,X32)
        | ~ v1_relat_1(X31) )
      & ( ~ r2_hidden(k4_tarski(X36,X37),X31)
        | ~ r2_hidden(X37,X32)
        | r2_hidden(X36,X33)
        | X33 != k10_relat_1(X31,X32)
        | ~ v1_relat_1(X31) )
      & ( ~ r2_hidden(esk4_3(X31,X38,X39),X39)
        | ~ r2_hidden(k4_tarski(esk4_3(X31,X38,X39),X41),X31)
        | ~ r2_hidden(X41,X38)
        | X39 = k10_relat_1(X31,X38)
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(k4_tarski(esk4_3(X31,X38,X39),esk5_3(X31,X38,X39)),X31)
        | r2_hidden(esk4_3(X31,X38,X39),X39)
        | X39 = k10_relat_1(X31,X38)
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(esk5_3(X31,X38,X39),X38)
        | r2_hidden(esk4_3(X31,X38,X39),X39)
        | X39 = k10_relat_1(X31,X38)
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_33,plain,(
    ! [X54,X55] :
      ( ~ v1_relat_1(X55)
      | k10_relat_1(X55,X54) = k10_relat_1(X55,k3_xboole_0(k2_relat_1(X55),X54)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).

fof(c_0_34,plain,(
    ! [X15,X16] :
      ( ( ~ r1_xboole_0(X15,X16)
        | k3_xboole_0(X15,X16) = k1_xboole_0 )
      & ( k3_xboole_0(X15,X16) != k1_xboole_0
        | r1_xboole_0(X15,X16) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_35,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | r1_xboole_0(X1,k2_relat_1(esk10_0))
    | ~ r2_hidden(esk2_2(X1,k2_relat_1(esk10_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),X3)
    | r2_hidden(esk2_2(k3_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_29])).

cnf(c_0_37,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_39,plain,(
    ! [X43,X44,X45,X47,X48,X49,X50,X52] :
      ( ( ~ r2_hidden(X45,X44)
        | r2_hidden(k4_tarski(esk6_3(X43,X44,X45),X45),X43)
        | X44 != k2_relat_1(X43) )
      & ( ~ r2_hidden(k4_tarski(X48,X47),X43)
        | r2_hidden(X47,X44)
        | X44 != k2_relat_1(X43) )
      & ( ~ r2_hidden(esk7_2(X49,X50),X50)
        | ~ r2_hidden(k4_tarski(X52,esk7_2(X49,X50)),X49)
        | X50 = k2_relat_1(X49) )
      & ( r2_hidden(esk7_2(X49,X50),X50)
        | r2_hidden(k4_tarski(esk8_2(X49,X50),esk7_2(X49,X50)),X49)
        | X50 = k2_relat_1(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_40,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k10_relat_1(X1,X2) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | r1_xboole_0(k3_xboole_0(esk9_0,X1),k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk8_2(X1,X2),esk7_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(esk3_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk10_0),k3_xboole_0(esk9_0,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_50,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk7_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X4,k10_relat_1(X1,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( k10_relat_1(esk10_0,k3_xboole_0(esk9_0,X1)) = k10_relat_1(esk10_0,k1_xboole_0)
    | k10_relat_1(esk10_0,esk9_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_53,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k10_relat_1(esk10_0,k1_xboole_0)
    | k10_relat_1(esk10_0,esk9_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_19]),c_0_49])])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_56,plain,
    ( r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_57,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | ~ r1_xboole_0(esk9_0,X1)
    | ~ r2_hidden(X2,k10_relat_1(esk10_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_49])])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk7_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_50,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | k10_relat_1(esk10_0,k1_xboole_0) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_61,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | ~ r1_xboole_0(esk9_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_63,plain,
    ( r2_hidden(esk6_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_38])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_49])]),c_0_44])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(X1,k2_relat_1(esk10_0))
    | ~ r2_hidden(esk2_2(X1,k2_relat_1(esk10_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_28])).

cnf(c_0_67,negated_conjecture,
    ( k10_relat_1(esk10_0,esk9_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(esk9_0,k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_29])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk10_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_64])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_68]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:16:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.40  # AutoSched0-Mode selected heuristic U_____100_C09_12_F1_SE_CS_SP_PS_S5PRR_RG_ND_S04AN
% 0.18/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.40  #
% 0.18/0.40  # Preprocessing time       : 0.028 s
% 0.18/0.40  # Presaturation interreduction done
% 0.18/0.40  
% 0.18/0.40  # Proof found!
% 0.18/0.40  # SZS status Theorem
% 0.18/0.40  # SZS output start CNFRefutation
% 0.18/0.40  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.18/0.40  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 0.18/0.40  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.18/0.40  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.18/0.40  fof(t55_zfmisc_1, axiom, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.18/0.40  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.18/0.40  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.18/0.40  fof(t168_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k10_relat_1(X2,X1)=k10_relat_1(X2,k3_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 0.18/0.40  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.18/0.40  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.18/0.40  fof(c_0_10, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7))&(r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k3_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k3_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))&(r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.18/0.40  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.18/0.40  fof(c_0_12, plain, ![X19, X20, X22, X23, X24]:((r1_xboole_0(X19,X20)|r2_hidden(esk2_2(X19,X20),k3_xboole_0(X19,X20)))&(~r2_hidden(X24,k3_xboole_0(X22,X23))|~r1_xboole_0(X22,X23))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.18/0.40  cnf(c_0_13, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.40  fof(c_0_14, plain, ![X17, X18]:(~r1_xboole_0(X17,X18)|r1_xboole_0(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.18/0.40  fof(c_0_15, negated_conjecture, (v1_relat_1(esk10_0)&((k10_relat_1(esk10_0,esk9_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk10_0),esk9_0))&(k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk10_0),esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.18/0.40  cnf(c_0_16, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.40  cnf(c_0_17, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_13])).
% 0.18/0.40  cnf(c_0_18, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.40  cnf(c_0_19, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.40  cnf(c_0_21, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.40  cnf(c_0_22, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.40  cnf(c_0_23, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(esk9_0,k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.40  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_20])).
% 0.18/0.40  cnf(c_0_25, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.40  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_21])).
% 0.18/0.40  cnf(c_0_27, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|~r2_hidden(X1,k2_relat_1(esk10_0))|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.40  cnf(c_0_28, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.40  cnf(c_0_29, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_26, c_0_25])).
% 0.18/0.40  fof(c_0_30, plain, ![X26, X27, X28]:(~r1_xboole_0(k2_tarski(X26,X27),X28)|~r2_hidden(X26,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).
% 0.18/0.40  fof(c_0_31, plain, ![X25]:r1_xboole_0(X25,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.18/0.40  fof(c_0_32, plain, ![X31, X32, X33, X34, X36, X37, X38, X39, X41]:((((r2_hidden(k4_tarski(X34,esk3_4(X31,X32,X33,X34)),X31)|~r2_hidden(X34,X33)|X33!=k10_relat_1(X31,X32)|~v1_relat_1(X31))&(r2_hidden(esk3_4(X31,X32,X33,X34),X32)|~r2_hidden(X34,X33)|X33!=k10_relat_1(X31,X32)|~v1_relat_1(X31)))&(~r2_hidden(k4_tarski(X36,X37),X31)|~r2_hidden(X37,X32)|r2_hidden(X36,X33)|X33!=k10_relat_1(X31,X32)|~v1_relat_1(X31)))&((~r2_hidden(esk4_3(X31,X38,X39),X39)|(~r2_hidden(k4_tarski(esk4_3(X31,X38,X39),X41),X31)|~r2_hidden(X41,X38))|X39=k10_relat_1(X31,X38)|~v1_relat_1(X31))&((r2_hidden(k4_tarski(esk4_3(X31,X38,X39),esk5_3(X31,X38,X39)),X31)|r2_hidden(esk4_3(X31,X38,X39),X39)|X39=k10_relat_1(X31,X38)|~v1_relat_1(X31))&(r2_hidden(esk5_3(X31,X38,X39),X38)|r2_hidden(esk4_3(X31,X38,X39),X39)|X39=k10_relat_1(X31,X38)|~v1_relat_1(X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.18/0.40  fof(c_0_33, plain, ![X54, X55]:(~v1_relat_1(X55)|k10_relat_1(X55,X54)=k10_relat_1(X55,k3_xboole_0(k2_relat_1(X55),X54))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t168_relat_1])])).
% 0.18/0.40  fof(c_0_34, plain, ![X15, X16]:((~r1_xboole_0(X15,X16)|k3_xboole_0(X15,X16)=k1_xboole_0)&(k3_xboole_0(X15,X16)!=k1_xboole_0|r1_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.18/0.40  cnf(c_0_35, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(X1,k2_relat_1(esk10_0))|~r2_hidden(esk2_2(X1,k2_relat_1(esk10_0)),esk9_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.18/0.40  cnf(c_0_36, plain, (r1_xboole_0(k3_xboole_0(X1,X2),X3)|r2_hidden(esk2_2(k3_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_26, c_0_29])).
% 0.18/0.40  cnf(c_0_37, plain, (~r1_xboole_0(k2_tarski(X1,X2),X3)|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.40  cnf(c_0_38, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.40  fof(c_0_39, plain, ![X43, X44, X45, X47, X48, X49, X50, X52]:(((~r2_hidden(X45,X44)|r2_hidden(k4_tarski(esk6_3(X43,X44,X45),X45),X43)|X44!=k2_relat_1(X43))&(~r2_hidden(k4_tarski(X48,X47),X43)|r2_hidden(X47,X44)|X44!=k2_relat_1(X43)))&((~r2_hidden(esk7_2(X49,X50),X50)|~r2_hidden(k4_tarski(X52,esk7_2(X49,X50)),X49)|X50=k2_relat_1(X49))&(r2_hidden(esk7_2(X49,X50),X50)|r2_hidden(k4_tarski(esk8_2(X49,X50),esk7_2(X49,X50)),X49)|X50=k2_relat_1(X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.18/0.40  cnf(c_0_40, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.40  cnf(c_0_41, plain, (k10_relat_1(X1,X2)=k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.40  cnf(c_0_42, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.40  cnf(c_0_43, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k3_xboole_0(esk9_0,X1),k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.18/0.40  cnf(c_0_44, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.18/0.40  cnf(c_0_45, plain, (r2_hidden(esk7_2(X1,X2),X2)|r2_hidden(k4_tarski(esk8_2(X1,X2),esk7_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.40  cnf(c_0_46, plain, (r2_hidden(esk3_4(X1,X2,k10_relat_1(X1,X2),X3),X2)|~v1_relat_1(X1)|~r2_hidden(X3,k10_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_40])).
% 0.18/0.40  cnf(c_0_47, plain, (k10_relat_1(X1,k1_xboole_0)=k10_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.18/0.40  cnf(c_0_48, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk10_0),k3_xboole_0(esk9_0,X1))), inference(spm,[status(thm)],[c_0_18, c_0_43])).
% 0.18/0.40  cnf(c_0_49, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_50, plain, (X1=k2_relat_1(k1_xboole_0)|r2_hidden(esk7_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.18/0.40  cnf(c_0_51, plain, (~v1_relat_1(X1)|~r1_xboole_0(X2,X3)|~r2_hidden(X4,k10_relat_1(X1,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_16, c_0_46])).
% 0.18/0.40  cnf(c_0_52, negated_conjecture, (k10_relat_1(esk10_0,k3_xboole_0(esk9_0,X1))=k10_relat_1(esk10_0,k1_xboole_0)|k10_relat_1(esk10_0,esk9_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.18/0.40  cnf(c_0_53, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_50])).
% 0.18/0.40  cnf(c_0_54, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k10_relat_1(esk10_0,k1_xboole_0)|k10_relat_1(esk10_0,esk9_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_19]), c_0_49])])).
% 0.18/0.40  cnf(c_0_55, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.40  cnf(c_0_56, plain, (r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.40  cnf(c_0_57, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|~r1_xboole_0(esk9_0,X1)|~r2_hidden(X2,k10_relat_1(esk10_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_49])])).
% 0.18/0.40  cnf(c_0_58, plain, (X1=k1_xboole_0|r2_hidden(esk7_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_50, c_0_53])).
% 0.18/0.40  cnf(c_0_59, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|k10_relat_1(esk10_0,k1_xboole_0)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_54])).
% 0.18/0.40  cnf(c_0_60, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_55])).
% 0.18/0.40  cnf(c_0_61, plain, (r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_56])).
% 0.18/0.40  cnf(c_0_62, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0|~r1_xboole_0(esk9_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 0.18/0.40  cnf(c_0_63, plain, (r2_hidden(esk6_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.18/0.40  cnf(c_0_64, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_38])).
% 0.18/0.40  cnf(c_0_65, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk10_0))|~r2_hidden(X1,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_49])]), c_0_44])).
% 0.18/0.40  cnf(c_0_66, negated_conjecture, (r1_xboole_0(X1,k2_relat_1(esk10_0))|~r2_hidden(esk2_2(X1,k2_relat_1(esk10_0)),esk9_0)), inference(spm,[status(thm)],[c_0_65, c_0_28])).
% 0.18/0.40  cnf(c_0_67, negated_conjecture, (k10_relat_1(esk10_0,esk9_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_68, negated_conjecture, (r1_xboole_0(esk9_0,k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_66, c_0_29])).
% 0.18/0.40  cnf(c_0_69, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk10_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_64])])).
% 0.18/0.40  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_68]), c_0_69]), ['proof']).
% 0.18/0.40  # SZS output end CNFRefutation
% 0.18/0.40  # Proof object total steps             : 71
% 0.18/0.40  # Proof object clause steps            : 50
% 0.18/0.40  # Proof object formula steps           : 21
% 0.18/0.40  # Proof object conjectures             : 22
% 0.18/0.40  # Proof object clause conjectures      : 19
% 0.18/0.40  # Proof object formula conjectures     : 3
% 0.18/0.40  # Proof object initial clauses used    : 17
% 0.18/0.40  # Proof object initial formulas used   : 10
% 0.18/0.40  # Proof object generating inferences   : 25
% 0.18/0.40  # Proof object simplifying inferences  : 20
% 0.18/0.40  # Training examples: 0 positive, 0 negative
% 0.18/0.40  # Parsed axioms                        : 12
% 0.18/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.40  # Initial clauses                      : 29
% 0.18/0.40  # Removed in clause preprocessing      : 0
% 0.18/0.40  # Initial clauses in saturation        : 29
% 0.18/0.40  # Processed clauses                    : 680
% 0.18/0.40  # ...of these trivial                  : 4
% 0.18/0.40  # ...subsumed                          : 467
% 0.18/0.40  # ...remaining for further processing  : 209
% 0.18/0.40  # Other redundant clauses eliminated   : 8
% 0.18/0.40  # Clauses deleted for lack of memory   : 0
% 0.18/0.40  # Backward-subsumed                    : 3
% 0.18/0.40  # Backward-rewritten                   : 34
% 0.18/0.40  # Generated clauses                    : 2095
% 0.18/0.40  # ...of the previous two non-trivial   : 1764
% 0.18/0.40  # Contextual simplify-reflections      : 1
% 0.18/0.40  # Paramodulations                      : 2080
% 0.18/0.40  # Factorizations                       : 7
% 0.18/0.40  # Equation resolutions                 : 8
% 0.18/0.40  # Propositional unsat checks           : 0
% 0.18/0.40  #    Propositional check models        : 0
% 0.18/0.40  #    Propositional check unsatisfiable : 0
% 0.18/0.40  #    Propositional clauses             : 0
% 0.18/0.40  #    Propositional clauses after purity: 0
% 0.18/0.40  #    Propositional unsat core size     : 0
% 0.18/0.40  #    Propositional preprocessing time  : 0.000
% 0.18/0.40  #    Propositional encoding time       : 0.000
% 0.18/0.40  #    Propositional solver time         : 0.000
% 0.18/0.40  #    Success case prop preproc time    : 0.000
% 0.18/0.40  #    Success case prop encoding time   : 0.000
% 0.18/0.40  #    Success case prop solver time     : 0.000
% 0.18/0.40  # Current number of processed clauses  : 135
% 0.18/0.40  #    Positive orientable unit clauses  : 10
% 0.18/0.40  #    Positive unorientable unit clauses: 0
% 0.18/0.40  #    Negative unit clauses             : 2
% 0.18/0.40  #    Non-unit-clauses                  : 123
% 0.18/0.40  # Current number of unprocessed clauses: 1086
% 0.18/0.40  # ...number of literals in the above   : 3196
% 0.18/0.40  # Current number of archived formulas  : 0
% 0.18/0.40  # Current number of archived clauses   : 66
% 0.18/0.40  # Clause-clause subsumption calls (NU) : 3949
% 0.18/0.40  # Rec. Clause-clause subsumption calls : 2257
% 0.18/0.40  # Non-unit clause-clause subsumptions  : 311
% 0.18/0.40  # Unit Clause-clause subsumption calls : 105
% 0.18/0.40  # Rewrite failures with RHS unbound    : 0
% 0.18/0.40  # BW rewrite match attempts            : 12
% 0.18/0.40  # BW rewrite match successes           : 6
% 0.18/0.40  # Condensation attempts                : 0
% 0.18/0.40  # Condensation successes               : 0
% 0.18/0.40  # Termbank termtop insertions          : 29142
% 0.18/0.40  
% 0.18/0.40  # -------------------------------------------------
% 0.18/0.40  # User time                : 0.068 s
% 0.18/0.40  # System time              : 0.004 s
% 0.18/0.40  # Total time               : 0.072 s
% 0.18/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
