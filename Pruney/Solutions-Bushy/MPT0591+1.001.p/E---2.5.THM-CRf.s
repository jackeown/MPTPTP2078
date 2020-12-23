%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0591+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:52 EST 2020

% Result     : Theorem 1.15s
% Output     : CNFRefutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   39 (  78 expanded)
%              Number of clauses        :   26 (  37 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  121 ( 292 expanded)
%              Number of equality atoms :   44 (  97 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t195_relat_1,conjecture,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(c_0_6,plain,(
    ! [X31,X32,X33,X34] :
      ( ( r2_hidden(X31,X33)
        | ~ r2_hidden(k4_tarski(X31,X32),k2_zfmisc_1(X33,X34)) )
      & ( r2_hidden(X32,X34)
        | ~ r2_hidden(k4_tarski(X31,X32),k2_zfmisc_1(X33,X34)) )
      & ( ~ r2_hidden(X31,X33)
        | ~ r2_hidden(X32,X34)
        | r2_hidden(k4_tarski(X31,X32),k2_zfmisc_1(X33,X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

fof(c_0_7,plain,(
    ! [X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( ~ r2_hidden(X22,X21)
        | r2_hidden(k4_tarski(esk5_3(X20,X21,X22),X22),X20)
        | X21 != k2_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X25,X24),X20)
        | r2_hidden(X24,X21)
        | X21 != k2_relat_1(X20) )
      & ( ~ r2_hidden(esk6_2(X26,X27),X27)
        | ~ r2_hidden(k4_tarski(X29,esk6_2(X26,X27)),X26)
        | X27 = k2_relat_1(X26) )
      & ( r2_hidden(esk6_2(X26,X27),X27)
        | r2_hidden(k4_tarski(esk7_2(X26,X27),esk6_2(X26,X27)),X26)
        | X27 = k2_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X9,X10,X11,X13,X14,X15,X16,X18] :
      ( ( ~ r2_hidden(X11,X10)
        | r2_hidden(k4_tarski(X11,esk2_3(X9,X10,X11)),X9)
        | X10 != k1_relat_1(X9) )
      & ( ~ r2_hidden(k4_tarski(X13,X14),X9)
        | r2_hidden(X13,X10)
        | X10 != k1_relat_1(X9) )
      & ( ~ r2_hidden(esk3_2(X15,X16),X16)
        | ~ r2_hidden(k4_tarski(esk3_2(X15,X16),X18),X15)
        | X16 = k1_relat_1(X15) )
      & ( r2_hidden(esk3_2(X15,X16),X16)
        | r2_hidden(k4_tarski(esk3_2(X15,X16),esk4_2(X15,X16)),X15)
        | X16 = k1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_11,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk6_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk6_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( X1 = k2_relat_1(k2_zfmisc_1(X2,X3))
    | r2_hidden(esk6_2(k2_zfmisc_1(X2,X3),X1),X1)
    | r2_hidden(esk6_2(k2_zfmisc_1(X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
              & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t195_relat_1])).

cnf(c_0_17,plain,
    ( X1 = k2_relat_1(k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk6_2(k2_zfmisc_1(X2,X3),X1),X1)
    | ~ r2_hidden(esk6_2(k2_zfmisc_1(X2,X3),X1),X3)
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | r2_hidden(esk6_2(k2_zfmisc_1(X1,X2),X2),X2) ),
    inference(ef,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_20,plain,
    ( X2 = k1_relat_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( X1 = k1_relat_1(k2_zfmisc_1(X2,X3))
    | r2_hidden(esk3_2(k2_zfmisc_1(X2,X3),X1),X1)
    | r2_hidden(esk3_2(k2_zfmisc_1(X2,X3),X1),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_22,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    & esk9_0 != k1_xboole_0
    & ( k1_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk8_0
      | k2_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk9_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_23,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( X1 = k1_relat_1(k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk3_2(k2_zfmisc_1(X2,X3),X1),X1)
    | ~ r2_hidden(esk3_2(k2_zfmisc_1(X2,X3),X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_12])).

cnf(c_0_26,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | r2_hidden(esk3_2(k2_zfmisc_1(X1,X2),X1),X1) ),
    inference(ef,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk8_0
    | k2_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_26])).

fof(c_0_30,plain,(
    ! [X35] :
      ( ~ v1_xboole_0(X35)
      | X35 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_31,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | k1_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk8_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( v1_xboole_0(esk9_0)
    | v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( v1_xboole_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_36]),c_0_37]),
    [proof]).

%------------------------------------------------------------------------------
