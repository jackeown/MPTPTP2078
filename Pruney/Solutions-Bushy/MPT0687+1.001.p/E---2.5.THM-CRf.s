%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0687+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:02 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 324 expanded)
%              Number of clauses        :   51 ( 172 expanded)
%              Number of leaves         :    8 (  71 expanded)
%              Depth                    :   17
%              Number of atoms          :  209 (1342 expanded)
%              Number of equality atoms :   48 ( 349 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(t142_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(c_0_8,plain,(
    ! [X31,X32,X33,X35,X36,X37,X38,X40] :
      ( ( ~ r2_hidden(X33,X32)
        | r2_hidden(k4_tarski(esk6_3(X31,X32,X33),X33),X31)
        | X32 != k2_relat_1(X31) )
      & ( ~ r2_hidden(k4_tarski(X36,X35),X31)
        | r2_hidden(X35,X32)
        | X32 != k2_relat_1(X31) )
      & ( ~ r2_hidden(esk7_2(X37,X38),X38)
        | ~ r2_hidden(k4_tarski(X40,esk7_2(X37,X38)),X37)
        | X38 = k2_relat_1(X37) )
      & ( r2_hidden(esk7_2(X37,X38),X38)
        | r2_hidden(k4_tarski(esk8_2(X37,X38),esk7_2(X37,X38)),X37)
        | X38 = k2_relat_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_9,plain,(
    ! [X43,X44] :
      ( ~ r2_hidden(X43,X44)
      | ~ v1_xboole_0(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v1_xboole_0(X27)
        | ~ r2_hidden(X28,X27) )
      & ( r2_hidden(esk5_1(X29),X29)
        | v1_xboole_0(X29) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_14,plain,(
    ! [X8,X9,X10,X11,X13,X14,X15,X16,X18] :
      ( ( r2_hidden(k4_tarski(X11,esk1_4(X8,X9,X10,X11)),X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k10_relat_1(X8,X9)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk1_4(X8,X9,X10,X11),X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k10_relat_1(X8,X9)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(X13,X14),X8)
        | ~ r2_hidden(X14,X9)
        | r2_hidden(X13,X10)
        | X10 != k10_relat_1(X8,X9)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(esk2_3(X8,X15,X16),X16)
        | ~ r2_hidden(k4_tarski(esk2_3(X8,X15,X16),X18),X8)
        | ~ r2_hidden(X18,X15)
        | X16 = k10_relat_1(X8,X15)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(k4_tarski(esk2_3(X8,X15,X16),esk3_3(X8,X15,X16)),X8)
        | r2_hidden(esk2_3(X8,X15,X16),X16)
        | X16 = k10_relat_1(X8,X15)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk3_3(X8,X15,X16),X15)
        | r2_hidden(esk2_3(X8,X15,X16),X16)
        | X16 = k10_relat_1(X8,X15)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_15,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X20
        | X21 != k1_tarski(X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k1_tarski(X20) )
      & ( ~ r2_hidden(esk4_2(X24,X25),X25)
        | esk4_2(X24,X25) != X24
        | X25 = k1_tarski(X24) )
      & ( r2_hidden(esk4_2(X24,X25),X25)
        | esk4_2(X24,X25) = X24
        | X25 = k1_tarski(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_16,plain,(
    ! [X42] :
      ( ~ v1_xboole_0(X42)
      | X42 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_17,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v1_xboole_0(k2_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_4(X1,X2,k10_relat_1(X1,X2),X3),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( esk1_4(X1,k1_tarski(X2),k10_relat_1(X1,k1_tarski(X2)),X3) = X2
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k10_relat_1(X1,k1_tarski(X2))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
        <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t142_funct_1])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_relat_1(k2_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_12])).

cnf(c_0_36,plain,
    ( k2_relat_1(k2_relat_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_24])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k10_relat_1(X2,k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_38,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & ( ~ r2_hidden(esk9_0,k2_relat_1(esk10_0))
      | k10_relat_1(esk10_0,k1_tarski(esk9_0)) = k1_xboole_0 )
    & ( r2_hidden(esk9_0,k2_relat_1(esk10_0))
      | k10_relat_1(esk10_0,k1_tarski(esk9_0)) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

fof(c_0_39,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ r2_hidden(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k2_relat_1(k1_tarski(k4_tarski(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_34])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( v1_xboole_0(k10_relat_1(X1,k1_tarski(X2)))
    | r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_18])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( ~ v1_xboole_0(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k10_relat_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_28])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k2_relat_1(k2_relat_1(k1_tarski(k4_tarski(X2,k4_tarski(X3,X1)))))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_40])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(k10_relat_1(esk10_0,k1_tarski(X1)))
    | r2_hidden(X1,k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( v1_xboole_0(k10_relat_1(X1,X2))
    | ~ v1_xboole_0(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_18])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(k2_relat_1(k2_relat_1(k1_tarski(k4_tarski(X1,k4_tarski(X2,X3))))),X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0)
    | r2_hidden(X1,k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_55,negated_conjecture,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( k10_relat_1(esk10_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_43])).

cnf(c_0_58,plain,
    ( r2_hidden(esk6_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_56,c_0_12])).

cnf(c_0_59,negated_conjecture,
    ( k10_relat_1(esk10_0,k1_tarski(esk9_0)) = k1_xboole_0
    | ~ r2_hidden(esk9_0,k2_relat_1(esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_57]),c_0_53]),c_0_43])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk6_3(esk10_0,k2_relat_1(esk10_0),X1),k1_xboole_0)
    | ~ r2_hidden(esk9_0,k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,k1_tarski(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_43])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk9_0,k2_relat_1(esk10_0))
    | k10_relat_1(esk10_0,k1_tarski(esk9_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_63,negated_conjecture,
    ( k10_relat_1(esk10_0,k1_tarski(X1)) = k1_xboole_0
    | r2_hidden(X1,k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,k1_tarski(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk9_0,k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,k1_tarski(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_65]),c_0_34])]),
    [proof]).

%------------------------------------------------------------------------------
