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
% DateTime   : Thu Dec  3 10:44:01 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 480 expanded)
%              Number of clauses        :   57 ( 229 expanded)
%              Number of leaves         :   12 ( 127 expanded)
%              Depth                    :   16
%              Number of atoms          :  221 (1776 expanded)
%              Number of equality atoms :   52 ( 681 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t6_xboole_0,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_12,plain,(
    ! [X22,X23,X24,X26,X27,X28,X29,X31] :
      ( ( r2_hidden(X24,esk4_3(X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k3_tarski(X22) )
      & ( r2_hidden(esk4_3(X22,X23,X24),X22)
        | ~ r2_hidden(X24,X23)
        | X23 != k3_tarski(X22) )
      & ( ~ r2_hidden(X26,X27)
        | ~ r2_hidden(X27,X22)
        | r2_hidden(X26,X23)
        | X23 != k3_tarski(X22) )
      & ( ~ r2_hidden(esk5_2(X28,X29),X29)
        | ~ r2_hidden(esk5_2(X28,X29),X31)
        | ~ r2_hidden(X31,X28)
        | X29 = k3_tarski(X28) )
      & ( r2_hidden(esk5_2(X28,X29),esk6_2(X28,X29))
        | r2_hidden(esk5_2(X28,X29),X29)
        | X29 = k3_tarski(X28) )
      & ( r2_hidden(esk6_2(X28,X29),X28)
        | r2_hidden(esk5_2(X28,X29),X29)
        | X29 = k3_tarski(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X33,X34,X35,X36] :
      ( ( r2_hidden(X33,X35)
        | ~ r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(X35,X36)) )
      & ( r2_hidden(X34,X36)
        | ~ r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(X35,X36)) )
      & ( ~ r2_hidden(X33,X35)
        | ~ r2_hidden(X34,X36)
        | r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(X35,X36)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_17,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k2_zfmisc_1(esk9_0,esk10_0)
    & esk7_0 != k1_xboole_0
    & esk8_0 != k1_xboole_0
    & ( esk7_0 != esk9_0
      | esk8_0 != esk10_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_18,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(esk4_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k2_zfmisc_1(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k3_tarski(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

cnf(c_0_24,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk9_0,esk10_0))
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_28,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r2_hidden(esk5_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,esk10_0)
    | ~ r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X2,esk7_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_2(k1_xboole_0,esk8_0),esk10_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_26])).

fof(c_0_37,plain,(
    ! [X17,X18] :
      ( ( r2_hidden(esk3_2(X17,X18),X18)
        | ~ r2_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk3_2(X17,X18),X17)
        | ~ r2_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk10_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk5_2(k1_xboole_0,esk8_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_31]),c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_31]),c_0_32])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(esk3_2(X1,X2),X1)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_44,plain,(
    ! [X37,X38,X39] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X38,X37),k2_zfmisc_1(X39,X37))
        | X37 = k1_xboole_0
        | r1_tarski(X38,X39) )
      & ( ~ r1_tarski(k2_zfmisc_1(X37,X38),k2_zfmisc_1(X37,X39))
        | X37 = k1_xboole_0
        | r1_tarski(X38,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk10_0)
    | ~ r2_hidden(X2,esk9_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk5_2(k1_xboole_0,esk7_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_31]),c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_xboole_0(esk7_0,X1)
    | ~ r2_hidden(esk3_2(esk7_0,X1),esk9_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_49,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | ~ r2_xboole_0(X15,X16) )
      & ( X15 != X16
        | ~ r2_xboole_0(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | X15 = X16
        | r2_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_50,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_51,plain,(
    ! [X40,X41,X42] :
      ( ( r1_tarski(k2_zfmisc_1(X40,X42),k2_zfmisc_1(X41,X42))
        | ~ r1_tarski(X40,X41) )
      & ( r1_tarski(k2_zfmisc_1(X42,X40),k2_zfmisc_1(X42,X41))
        | ~ r1_tarski(X40,X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

fof(c_0_52,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_xboole_0(esk7_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk9_0,esk10_0),k2_zfmisc_1(X1,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_21]),c_0_32])).

cnf(c_0_57,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_xboole_0(esk8_0,X1)
    | ~ r2_hidden(esk3_2(esk8_0,X1),esk10_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_53])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_61,negated_conjecture,
    ( esk7_0 = esk9_0
    | ~ r1_tarski(esk7_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk7_0,esk9_0)
    | ~ r1_tarski(esk10_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r2_hidden(esk2_2(X1,esk8_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_53])).

cnf(c_0_64,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_xboole_0(esk8_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_48])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk8_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk9_0,esk10_0),k2_zfmisc_1(esk7_0,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_21]),c_0_35])).

cnf(c_0_67,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_68,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_69,negated_conjecture,
    ( esk7_0 = esk9_0
    | ~ r1_tarski(esk10_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk10_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( esk8_0 = esk10_0
    | ~ r1_tarski(esk8_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_55])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk8_0,esk10_0)
    | ~ r1_tarski(esk9_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( esk7_0 != esk9_0
    | esk8_0 != esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_75,negated_conjecture,
    ( esk7_0 = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_76,negated_conjecture,
    ( esk8_0 = esk10_0
    | ~ r1_tarski(esk9_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( esk8_0 != esk10_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_75]),c_0_77])]),c_0_78]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.51  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.20/0.51  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.51  #
% 0.20/0.51  # Preprocessing time       : 0.027 s
% 0.20/0.51  
% 0.20/0.51  # Proof found!
% 0.20/0.51  # SZS status Theorem
% 0.20/0.51  # SZS output start CNFRefutation
% 0.20/0.51  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.20/0.51  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.20/0.51  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.51  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.20/0.51  fof(t2_zfmisc_1, axiom, k3_tarski(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 0.20/0.51  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.51  fof(t6_xboole_0, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&![X3]:~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 0.20/0.51  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.20/0.51  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.20/0.51  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 0.20/0.51  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.51  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.51  fof(c_0_12, plain, ![X22, X23, X24, X26, X27, X28, X29, X31]:((((r2_hidden(X24,esk4_3(X22,X23,X24))|~r2_hidden(X24,X23)|X23!=k3_tarski(X22))&(r2_hidden(esk4_3(X22,X23,X24),X22)|~r2_hidden(X24,X23)|X23!=k3_tarski(X22)))&(~r2_hidden(X26,X27)|~r2_hidden(X27,X22)|r2_hidden(X26,X23)|X23!=k3_tarski(X22)))&((~r2_hidden(esk5_2(X28,X29),X29)|(~r2_hidden(esk5_2(X28,X29),X31)|~r2_hidden(X31,X28))|X29=k3_tarski(X28))&((r2_hidden(esk5_2(X28,X29),esk6_2(X28,X29))|r2_hidden(esk5_2(X28,X29),X29)|X29=k3_tarski(X28))&(r2_hidden(esk6_2(X28,X29),X28)|r2_hidden(esk5_2(X28,X29),X29)|X29=k3_tarski(X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.20/0.51  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 0.20/0.51  fof(c_0_14, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.51  cnf(c_0_15, plain, (r2_hidden(esk4_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.51  fof(c_0_16, plain, ![X33, X34, X35, X36]:(((r2_hidden(X33,X35)|~r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(X35,X36)))&(r2_hidden(X34,X36)|~r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(X35,X36))))&(~r2_hidden(X33,X35)|~r2_hidden(X34,X36)|r2_hidden(k4_tarski(X33,X34),k2_zfmisc_1(X35,X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.20/0.51  fof(c_0_17, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k2_zfmisc_1(esk9_0,esk10_0)&((esk7_0!=k1_xboole_0&esk8_0!=k1_xboole_0)&(esk7_0!=esk9_0|esk8_0!=esk10_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.20/0.51  cnf(c_0_18, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.51  cnf(c_0_19, plain, (r2_hidden(esk4_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_15])).
% 0.20/0.51  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.51  cnf(c_0_21, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k2_zfmisc_1(esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.51  cnf(c_0_22, plain, (~r2_hidden(X1,k3_tarski(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.51  cnf(c_0_23, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).
% 0.20/0.51  cnf(c_0_24, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.51  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.51  cnf(c_0_26, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk9_0,esk10_0))|~r2_hidden(X2,esk8_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.51  cnf(c_0_27, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.20/0.51  cnf(c_0_28, plain, (r2_hidden(esk6_2(X1,X2),X1)|r2_hidden(esk5_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.51  cnf(c_0_29, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.51  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,esk10_0)|~r2_hidden(X1,esk8_0)|~r2_hidden(X2,esk7_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.51  cnf(c_0_31, plain, (X1=k1_xboole_0|r2_hidden(esk5_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_23])).
% 0.20/0.51  cnf(c_0_32, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.51  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_29, c_0_21])).
% 0.20/0.51  cnf(c_0_34, negated_conjecture, (r2_hidden(esk5_2(k1_xboole_0,esk8_0),esk10_0)|~r2_hidden(X1,esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.20/0.51  cnf(c_0_35, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.51  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X2,esk8_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_29, c_0_26])).
% 0.20/0.51  fof(c_0_37, plain, ![X17, X18]:((r2_hidden(esk3_2(X17,X18),X18)|~r2_xboole_0(X17,X18))&(~r2_hidden(esk3_2(X17,X18),X17)|~r2_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).
% 0.20/0.51  cnf(c_0_38, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X2,esk10_0)|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_33, c_0_20])).
% 0.20/0.51  cnf(c_0_39, negated_conjecture, (r2_hidden(esk5_2(k1_xboole_0,esk8_0),esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_31]), c_0_35])).
% 0.20/0.51  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_25, c_0_21])).
% 0.20/0.51  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X1,esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_31]), c_0_32])).
% 0.20/0.51  cnf(c_0_42, plain, (~r2_hidden(esk3_2(X1,X2),X1)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.51  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.51  fof(c_0_44, plain, ![X37, X38, X39]:((~r1_tarski(k2_zfmisc_1(X38,X37),k2_zfmisc_1(X39,X37))|X37=k1_xboole_0|r1_tarski(X38,X39))&(~r1_tarski(k2_zfmisc_1(X37,X38),k2_zfmisc_1(X37,X39))|X37=k1_xboole_0|r1_tarski(X38,X39))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.20/0.51  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk10_0)|~r2_hidden(X2,esk9_0)), inference(spm,[status(thm)],[c_0_40, c_0_20])).
% 0.20/0.51  cnf(c_0_46, negated_conjecture, (r2_hidden(esk5_2(k1_xboole_0,esk7_0),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_31]), c_0_35])).
% 0.20/0.51  cnf(c_0_47, negated_conjecture, (~r2_xboole_0(esk7_0,X1)|~r2_hidden(esk3_2(esk7_0,X1),esk9_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.51  cnf(c_0_48, plain, (r2_hidden(esk3_2(X1,X2),X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.51  fof(c_0_49, plain, ![X15, X16]:(((r1_tarski(X15,X16)|~r2_xboole_0(X15,X16))&(X15!=X16|~r2_xboole_0(X15,X16)))&(~r1_tarski(X15,X16)|X15=X16|r2_xboole_0(X15,X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.20/0.51  cnf(c_0_50, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.51  fof(c_0_51, plain, ![X40, X41, X42]:((r1_tarski(k2_zfmisc_1(X40,X42),k2_zfmisc_1(X41,X42))|~r1_tarski(X40,X41))&(r1_tarski(k2_zfmisc_1(X42,X40),k2_zfmisc_1(X42,X41))|~r1_tarski(X40,X41))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 0.20/0.51  fof(c_0_52, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.51  cnf(c_0_53, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.51  cnf(c_0_54, negated_conjecture, (~r2_xboole_0(esk7_0,esk9_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.51  cnf(c_0_55, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.51  cnf(c_0_56, negated_conjecture, (r1_tarski(esk7_0,X1)|~r1_tarski(k2_zfmisc_1(esk9_0,esk10_0),k2_zfmisc_1(X1,esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_21]), c_0_32])).
% 0.20/0.51  cnf(c_0_57, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.51  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.51  cnf(c_0_59, negated_conjecture, (~r2_xboole_0(esk8_0,X1)|~r2_hidden(esk3_2(esk8_0,X1),esk10_0)), inference(spm,[status(thm)],[c_0_42, c_0_53])).
% 0.20/0.51  cnf(c_0_60, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.51  cnf(c_0_61, negated_conjecture, (esk7_0=esk9_0|~r1_tarski(esk7_0,esk9_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.51  cnf(c_0_62, negated_conjecture, (r1_tarski(esk7_0,esk9_0)|~r1_tarski(esk10_0,esk8_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.51  cnf(c_0_63, negated_conjecture, (r1_tarski(X1,esk8_0)|~r2_hidden(esk2_2(X1,esk8_0),esk10_0)), inference(spm,[status(thm)],[c_0_58, c_0_53])).
% 0.20/0.51  cnf(c_0_64, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.51  cnf(c_0_65, negated_conjecture, (~r2_xboole_0(esk8_0,esk10_0)), inference(spm,[status(thm)],[c_0_59, c_0_48])).
% 0.20/0.51  cnf(c_0_66, negated_conjecture, (r1_tarski(esk8_0,X1)|~r1_tarski(k2_zfmisc_1(esk9_0,esk10_0),k2_zfmisc_1(esk7_0,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_21]), c_0_35])).
% 0.20/0.51  cnf(c_0_67, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.51  fof(c_0_68, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.51  cnf(c_0_69, negated_conjecture, (esk7_0=esk9_0|~r1_tarski(esk10_0,esk8_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.51  cnf(c_0_70, negated_conjecture, (r1_tarski(esk10_0,esk8_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.51  cnf(c_0_71, negated_conjecture, (esk8_0=esk10_0|~r1_tarski(esk8_0,esk10_0)), inference(spm,[status(thm)],[c_0_65, c_0_55])).
% 0.20/0.51  cnf(c_0_72, negated_conjecture, (r1_tarski(esk8_0,esk10_0)|~r1_tarski(esk9_0,esk7_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.51  cnf(c_0_73, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.51  cnf(c_0_74, negated_conjecture, (esk7_0!=esk9_0|esk8_0!=esk10_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.51  cnf(c_0_75, negated_conjecture, (esk7_0=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])])).
% 0.20/0.51  cnf(c_0_76, negated_conjecture, (esk8_0=esk10_0|~r1_tarski(esk9_0,esk7_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.51  cnf(c_0_77, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_73])).
% 0.20/0.51  cnf(c_0_78, negated_conjecture, (esk8_0!=esk10_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75])])).
% 0.20/0.51  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_75]), c_0_77])]), c_0_78]), ['proof']).
% 0.20/0.51  # SZS output end CNFRefutation
% 0.20/0.51  # Proof object total steps             : 80
% 0.20/0.51  # Proof object clause steps            : 57
% 0.20/0.51  # Proof object formula steps           : 23
% 0.20/0.51  # Proof object conjectures             : 37
% 0.20/0.51  # Proof object clause conjectures      : 34
% 0.20/0.51  # Proof object formula conjectures     : 3
% 0.20/0.51  # Proof object initial clauses used    : 22
% 0.20/0.51  # Proof object initial formulas used   : 12
% 0.20/0.51  # Proof object generating inferences   : 30
% 0.20/0.51  # Proof object simplifying inferences  : 19
% 0.20/0.51  # Training examples: 0 positive, 0 negative
% 0.20/0.51  # Parsed axioms                        : 12
% 0.20/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.51  # Initial clauses                      : 32
% 0.20/0.51  # Removed in clause preprocessing      : 0
% 0.20/0.51  # Initial clauses in saturation        : 32
% 0.20/0.51  # Processed clauses                    : 1633
% 0.20/0.51  # ...of these trivial                  : 4
% 0.20/0.51  # ...subsumed                          : 1094
% 0.20/0.51  # ...remaining for further processing  : 534
% 0.20/0.51  # Other redundant clauses eliminated   : 6
% 0.20/0.51  # Clauses deleted for lack of memory   : 0
% 0.20/0.51  # Backward-subsumed                    : 228
% 0.20/0.51  # Backward-rewritten                   : 96
% 0.20/0.51  # Generated clauses                    : 8058
% 0.20/0.51  # ...of the previous two non-trivial   : 7447
% 0.20/0.51  # Contextual simplify-reflections      : 13
% 0.20/0.51  # Paramodulations                      : 8051
% 0.20/0.51  # Factorizations                       : 0
% 0.20/0.51  # Equation resolutions                 : 6
% 0.20/0.51  # Propositional unsat checks           : 0
% 0.20/0.51  #    Propositional check models        : 0
% 0.20/0.51  #    Propositional check unsatisfiable : 0
% 0.20/0.51  #    Propositional clauses             : 0
% 0.20/0.51  #    Propositional clauses after purity: 0
% 0.20/0.51  #    Propositional unsat core size     : 0
% 0.20/0.51  #    Propositional preprocessing time  : 0.000
% 0.20/0.51  #    Propositional encoding time       : 0.000
% 0.20/0.51  #    Propositional solver time         : 0.000
% 0.20/0.51  #    Success case prop preproc time    : 0.000
% 0.20/0.51  #    Success case prop encoding time   : 0.000
% 0.20/0.51  #    Success case prop solver time     : 0.000
% 0.20/0.51  # Current number of processed clauses  : 203
% 0.20/0.51  #    Positive orientable unit clauses  : 7
% 0.20/0.51  #    Positive unorientable unit clauses: 0
% 0.20/0.51  #    Negative unit clauses             : 10
% 0.20/0.51  #    Non-unit-clauses                  : 186
% 0.20/0.51  # Current number of unprocessed clauses: 5650
% 0.20/0.51  # ...number of literals in the above   : 23948
% 0.20/0.51  # Current number of archived formulas  : 0
% 0.20/0.51  # Current number of archived clauses   : 325
% 0.20/0.51  # Clause-clause subsumption calls (NU) : 24923
% 0.20/0.51  # Rec. Clause-clause subsumption calls : 19453
% 0.20/0.51  # Non-unit clause-clause subsumptions  : 831
% 0.20/0.51  # Unit Clause-clause subsumption calls : 1950
% 0.20/0.51  # Rewrite failures with RHS unbound    : 0
% 0.20/0.51  # BW rewrite match attempts            : 12
% 0.20/0.51  # BW rewrite match successes           : 4
% 0.20/0.51  # Condensation attempts                : 0
% 0.20/0.51  # Condensation successes               : 0
% 0.20/0.51  # Termbank termtop insertions          : 105669
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.156 s
% 0.20/0.51  # System time              : 0.006 s
% 0.20/0.51  # Total time               : 0.163 s
% 0.20/0.51  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
