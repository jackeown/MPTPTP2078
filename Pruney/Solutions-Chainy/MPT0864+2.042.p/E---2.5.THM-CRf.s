%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:23 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 281 expanded)
%              Number of clauses        :   47 ( 134 expanded)
%              Number of leaves         :   12 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  179 ( 695 expanded)
%              Number of equality atoms :  119 ( 478 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t34_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))
    <=> ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_12,plain,(
    ! [X21,X22] : ~ r2_hidden(X21,k2_zfmisc_1(X21,X22)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

fof(c_0_13,plain,(
    ! [X19,X20] :
      ( ( k2_zfmisc_1(X19,X20) != k1_xboole_0
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X19,X20) = k1_xboole_0 )
      & ( X20 != k1_xboole_0
        | k2_zfmisc_1(X19,X20) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_14,plain,(
    ! [X23,X24,X25,X26] :
      ( ( X23 = X25
        | ~ r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(k1_tarski(X25),k1_tarski(X26))) )
      & ( X24 = X26
        | ~ r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(k1_tarski(X25),k1_tarski(X26))) )
      & ( X23 != X25
        | X24 != X26
        | r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(k1_tarski(X25),k1_tarski(X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).

fof(c_0_15,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X27,X28,X29] :
      ( k2_zfmisc_1(k1_tarski(X27),k2_tarski(X28,X29)) = k2_tarski(k4_tarski(X27,X28),k4_tarski(X27,X29))
      & k2_zfmisc_1(k2_tarski(X27,X28),k1_tarski(X29)) = k2_tarski(k4_tarski(X27,X29),k4_tarski(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
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

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4)))
    | X1 != X2
    | X3 != X4 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

cnf(c_0_24,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X4,X4)))
    | X3 != X4
    | X1 != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21])).

cnf(c_0_28,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

fof(c_0_29,negated_conjecture,
    ( esk10_0 = k4_tarski(esk11_0,esk12_0)
    & ( esk10_0 = k1_mcart_1(esk10_0)
      | esk10_0 = k2_mcart_1(esk10_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_30,plain,
    ( X1 != k2_relat_1(k1_xboole_0)
    | X2 != k1_xboole_0
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_31,plain,(
    ! [X54,X56,X57] :
      ( ( r2_hidden(esk9_1(X54),X54)
        | X54 = k1_xboole_0 )
      & ( ~ r2_hidden(X56,X54)
        | esk9_1(X54) != k4_tarski(X56,X57)
        | X54 = k1_xboole_0 )
      & ( ~ r2_hidden(X57,X54)
        | esk9_1(X54) != k4_tarski(X56,X57)
        | X54 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

fof(c_0_32,plain,(
    ! [X52,X53] :
      ( k1_mcart_1(k4_tarski(X52,X53)) = X52
      & k2_mcart_1(k4_tarski(X52,X53)) = X53 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])])])).

cnf(c_0_35,negated_conjecture,
    ( esk10_0 = k4_tarski(esk11_0,esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k2_relat_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(esk9_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X9
        | X12 = X10
        | X11 != k2_tarski(X9,X10) )
      & ( X13 != X9
        | r2_hidden(X13,X11)
        | X11 != k2_tarski(X9,X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k2_tarski(X9,X10) )
      & ( esk2_3(X14,X15,X16) != X14
        | ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k2_tarski(X14,X15) )
      & ( esk2_3(X14,X15,X16) != X15
        | ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k2_tarski(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X16)
        | esk2_3(X14,X15,X16) = X14
        | esk2_3(X14,X15,X16) = X15
        | X16 = k2_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( X1 != k2_relat_1(X2)
    | ~ r2_hidden(X3,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk10_0,k2_tarski(esk10_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_21])).

cnf(c_0_46,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( esk10_0 = k1_mcart_1(esk10_0)
    | esk10_0 = k2_mcart_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_48,negated_conjecture,
    ( k1_mcart_1(esk10_0) = esk11_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( k2_relat_1(X1) != k2_tarski(esk10_0,esk10_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_51,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( X1 = X2
    | X3 != k2_tarski(X2,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(ef,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( ~ v1_xboole_0(k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_54,plain,
    ( k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X2)) = k1_xboole_0
    | k2_tarski(X2,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k2_mcart_1(esk10_0) = esk12_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( k2_mcart_1(esk10_0) = esk10_0
    | esk11_0 = esk10_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk9_1(X2) != k4_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_58,negated_conjecture,
    ( k2_tarski(esk10_0,esk10_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( k2_tarski(X1,X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_50])])).

cnf(c_0_61,negated_conjecture,
    ( esk11_0 = esk10_0
    | esk12_0 = esk10_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( esk9_1(k2_tarski(esk10_0,esk10_0)) != k4_tarski(X1,esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_42]),c_0_58])).

cnf(c_0_63,plain,
    ( esk9_1(k2_tarski(X1,X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_37]),c_0_60])).

cnf(c_0_64,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk9_1(X2) != k4_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_65,negated_conjecture,
    ( k4_tarski(esk11_0,esk10_0) = esk10_0
    | esk11_0 = esk10_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( k4_tarski(X1,esk10_0) != esk10_0 ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( esk9_1(k2_tarski(esk10_0,esk10_0)) != k4_tarski(esk10_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_42]),c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( esk11_0 = esk10_0 ),
    inference(sr,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( k4_tarski(esk10_0,X1) != esk10_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_68]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:44:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.19/0.41  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.029 s
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.19/0.41  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.41  fof(t34_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))<=>(X1=X3&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 0.19/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.41  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.19/0.41  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.41  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.19/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.41  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.19/0.41  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.19/0.41  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.19/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.41  fof(c_0_12, plain, ![X21, X22]:~r2_hidden(X21,k2_zfmisc_1(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.19/0.41  fof(c_0_13, plain, ![X19, X20]:((k2_zfmisc_1(X19,X20)!=k1_xboole_0|(X19=k1_xboole_0|X20=k1_xboole_0))&((X19!=k1_xboole_0|k2_zfmisc_1(X19,X20)=k1_xboole_0)&(X20!=k1_xboole_0|k2_zfmisc_1(X19,X20)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.41  fof(c_0_14, plain, ![X23, X24, X25, X26]:(((X23=X25|~r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(k1_tarski(X25),k1_tarski(X26))))&(X24=X26|~r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(k1_tarski(X25),k1_tarski(X26)))))&(X23!=X25|X24!=X26|r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(k1_tarski(X25),k1_tarski(X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).
% 0.19/0.41  fof(c_0_15, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.41  fof(c_0_16, plain, ![X27, X28, X29]:(k2_zfmisc_1(k1_tarski(X27),k2_tarski(X28,X29))=k2_tarski(k4_tarski(X27,X28),k4_tarski(X27,X29))&k2_zfmisc_1(k2_tarski(X27,X28),k1_tarski(X29))=k2_tarski(k4_tarski(X27,X29),k4_tarski(X28,X29))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.19/0.41  cnf(c_0_17, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_18, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  fof(c_0_19, plain, ![X41, X42, X43, X45, X46, X47, X48, X50]:(((~r2_hidden(X43,X42)|r2_hidden(k4_tarski(esk6_3(X41,X42,X43),X43),X41)|X42!=k2_relat_1(X41))&(~r2_hidden(k4_tarski(X46,X45),X41)|r2_hidden(X45,X42)|X42!=k2_relat_1(X41)))&((~r2_hidden(esk7_2(X47,X48),X48)|~r2_hidden(k4_tarski(X50,esk7_2(X47,X48)),X47)|X48=k2_relat_1(X47))&(r2_hidden(esk7_2(X47,X48),X48)|r2_hidden(k4_tarski(esk8_2(X47,X48),esk7_2(X47,X48)),X47)|X48=k2_relat_1(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.41  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4)))|X1!=X2|X3!=X4), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_22, plain, (k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  fof(c_0_23, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.19/0.41  cnf(c_0_24, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.41  cnf(c_0_25, plain, (r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  fof(c_0_26, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.41  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X4,X4)))|X3!=X4|X1!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_21])).
% 0.19/0.41  cnf(c_0_28, plain, (k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 0.19/0.41  fof(c_0_29, negated_conjecture, (esk10_0=k4_tarski(esk11_0,esk12_0)&(esk10_0=k1_mcart_1(esk10_0)|esk10_0=k2_mcart_1(esk10_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.19/0.41  cnf(c_0_30, plain, (X1!=k2_relat_1(k1_xboole_0)|X2!=k1_xboole_0|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.41  fof(c_0_31, plain, ![X54, X56, X57]:((r2_hidden(esk9_1(X54),X54)|X54=k1_xboole_0)&((~r2_hidden(X56,X54)|esk9_1(X54)!=k4_tarski(X56,X57)|X54=k1_xboole_0)&(~r2_hidden(X57,X54)|esk9_1(X54)!=k4_tarski(X56,X57)|X54=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.19/0.41  fof(c_0_32, plain, ![X52, X53]:(k1_mcart_1(k4_tarski(X52,X53))=X52&k2_mcart_1(k4_tarski(X52,X53))=X53), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.19/0.41  cnf(c_0_33, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.41  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,X2),k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)))), inference(er,[status(thm)],[inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28])])])).
% 0.19/0.41  cnf(c_0_35, negated_conjecture, (esk10_0=k4_tarski(esk11_0,esk12_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_36, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k2_relat_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_37, plain, (r2_hidden(esk9_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  fof(c_0_38, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X12,X11)|(X12=X9|X12=X10)|X11!=k2_tarski(X9,X10))&((X13!=X9|r2_hidden(X13,X11)|X11!=k2_tarski(X9,X10))&(X13!=X10|r2_hidden(X13,X11)|X11!=k2_tarski(X9,X10))))&(((esk2_3(X14,X15,X16)!=X14|~r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k2_tarski(X14,X15))&(esk2_3(X14,X15,X16)!=X15|~r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k2_tarski(X14,X15)))&(r2_hidden(esk2_3(X14,X15,X16),X16)|(esk2_3(X14,X15,X16)=X14|esk2_3(X14,X15,X16)=X15)|X16=k2_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.19/0.41  cnf(c_0_39, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_40, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.41  cnf(c_0_41, plain, (X1!=k2_relat_1(X2)|~r2_hidden(X3,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_33, c_0_25])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (r2_hidden(esk10_0,k2_tarski(esk10_0,esk10_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.41  cnf(c_0_43, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.41  cnf(c_0_44, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.41  cnf(c_0_45, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[c_0_39, c_0_21])).
% 0.19/0.41  cnf(c_0_46, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (esk10_0=k1_mcart_1(esk10_0)|esk10_0=k2_mcart_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_48, negated_conjecture, (k1_mcart_1(esk10_0)=esk11_0), inference(spm,[status(thm)],[c_0_40, c_0_35])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (k2_relat_1(X1)!=k2_tarski(esk10_0,esk10_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.41  cnf(c_0_50, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.41  cnf(c_0_51, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_43])).
% 0.19/0.41  cnf(c_0_52, plain, (X1=X2|X3!=k2_tarski(X2,X2)|~r2_hidden(X1,X3)), inference(ef,[status(thm)],[c_0_44])).
% 0.19/0.41  cnf(c_0_53, plain, (~v1_xboole_0(k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.41  cnf(c_0_54, plain, (k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X2))=k1_xboole_0|k2_tarski(X2,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_45])).
% 0.19/0.41  cnf(c_0_55, negated_conjecture, (k2_mcart_1(esk10_0)=esk12_0), inference(spm,[status(thm)],[c_0_46, c_0_35])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (k2_mcart_1(esk10_0)=esk10_0|esk11_0=esk10_0), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.41  cnf(c_0_57, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk9_1(X2)!=k4_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (k2_tarski(esk10_0,esk10_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.19/0.41  cnf(c_0_59, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_52])).
% 0.19/0.41  cnf(c_0_60, plain, (k2_tarski(X1,X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_50])])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (esk11_0=esk10_0|esk12_0=esk10_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (esk9_1(k2_tarski(esk10_0,esk10_0))!=k4_tarski(X1,esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_42]), c_0_58])).
% 0.19/0.41  cnf(c_0_63, plain, (esk9_1(k2_tarski(X1,X1))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_37]), c_0_60])).
% 0.19/0.41  cnf(c_0_64, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk9_1(X2)!=k4_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_65, negated_conjecture, (k4_tarski(esk11_0,esk10_0)=esk10_0|esk11_0=esk10_0), inference(spm,[status(thm)],[c_0_35, c_0_61])).
% 0.19/0.41  cnf(c_0_66, negated_conjecture, (k4_tarski(X1,esk10_0)!=esk10_0), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.41  cnf(c_0_67, negated_conjecture, (esk9_1(k2_tarski(esk10_0,esk10_0))!=k4_tarski(esk10_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_42]), c_0_58])).
% 0.19/0.41  cnf(c_0_68, negated_conjecture, (esk11_0=esk10_0), inference(sr,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, (k4_tarski(esk10_0,X1)!=esk10_0), inference(rw,[status(thm)],[c_0_67, c_0_63])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_68]), c_0_69]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 71
% 0.19/0.41  # Proof object clause steps            : 47
% 0.19/0.41  # Proof object formula steps           : 24
% 0.19/0.41  # Proof object conjectures             : 19
% 0.19/0.41  # Proof object clause conjectures      : 16
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 17
% 0.19/0.41  # Proof object initial formulas used   : 12
% 0.19/0.41  # Proof object generating inferences   : 21
% 0.19/0.41  # Proof object simplifying inferences  : 19
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 13
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 34
% 0.19/0.41  # Removed in clause preprocessing      : 1
% 0.19/0.41  # Initial clauses in saturation        : 33
% 0.19/0.41  # Processed clauses                    : 414
% 0.19/0.41  # ...of these trivial                  : 11
% 0.19/0.41  # ...subsumed                          : 147
% 0.19/0.41  # ...remaining for further processing  : 255
% 0.19/0.41  # Other redundant clauses eliminated   : 28
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 26
% 0.19/0.41  # Backward-rewritten                   : 57
% 0.19/0.41  # Generated clauses                    : 1487
% 0.19/0.41  # ...of the previous two non-trivial   : 1418
% 0.19/0.41  # Contextual simplify-reflections      : 4
% 0.19/0.41  # Paramodulations                      : 1345
% 0.19/0.41  # Factorizations                       : 62
% 0.19/0.41  # Equation resolutions                 : 80
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
% 0.19/0.41  # Current number of processed clauses  : 168
% 0.19/0.41  #    Positive orientable unit clauses  : 15
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 16
% 0.19/0.41  #    Non-unit-clauses                  : 137
% 0.19/0.41  # Current number of unprocessed clauses: 1003
% 0.19/0.41  # ...number of literals in the above   : 3874
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 85
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 2144
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 1496
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 69
% 0.19/0.41  # Unit Clause-clause subsumption calls : 191
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 51
% 0.19/0.41  # BW rewrite match successes           : 7
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 16262
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.066 s
% 0.19/0.41  # System time              : 0.007 s
% 0.19/0.41  # Total time               : 0.073 s
% 0.19/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
