%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:07 EST 2020

% Result     : Theorem 4.91s
% Output     : CNFRefutation 4.91s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 295 expanded)
%              Number of clauses        :   58 ( 147 expanded)
%              Number of leaves         :    7 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  200 (1054 expanded)
%              Number of equality atoms :   60 ( 205 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t195_relat_1,conjecture,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(c_0_7,plain,(
    ! [X18,X19,X20,X22,X23,X24,X25,X27] :
      ( ( ~ r2_hidden(X20,X19)
        | r2_hidden(k4_tarski(X20,esk2_3(X18,X19,X20)),X18)
        | X19 != k1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X22,X23),X18)
        | r2_hidden(X22,X19)
        | X19 != k1_relat_1(X18) )
      & ( ~ r2_hidden(esk3_2(X24,X25),X25)
        | ~ r2_hidden(k4_tarski(esk3_2(X24,X25),X27),X24)
        | X25 = k1_relat_1(X24) )
      & ( r2_hidden(esk3_2(X24,X25),X25)
        | r2_hidden(k4_tarski(esk3_2(X24,X25),esk4_2(X24,X25)),X24)
        | X25 = k1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X14,X15,X16,X17] :
      ( ( r2_hidden(X14,X16)
        | ~ r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17)) )
      & ( r2_hidden(X15,X17)
        | ~ r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17)) )
      & ( ~ r2_hidden(X14,X16)
        | ~ r2_hidden(X15,X17)
        | r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X3)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_15,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_16,plain,(
    ! [X29,X30,X31,X33,X34,X35,X36,X38] :
      ( ( ~ r2_hidden(X31,X30)
        | r2_hidden(k4_tarski(esk5_3(X29,X30,X31),X31),X29)
        | X30 != k2_relat_1(X29) )
      & ( ~ r2_hidden(k4_tarski(X34,X33),X29)
        | r2_hidden(X33,X30)
        | X30 != k2_relat_1(X29) )
      & ( ~ r2_hidden(esk6_2(X35,X36),X36)
        | ~ r2_hidden(k4_tarski(X38,esk6_2(X35,X36)),X35)
        | X36 = k2_relat_1(X35) )
      & ( r2_hidden(esk6_2(X35,X36),X36)
        | r2_hidden(k4_tarski(esk7_2(X35,X36),esk6_2(X35,X36)),X35)
        | X36 = k2_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ r1_tarski(X3,k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_23,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k1_relat_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_2(k1_relat_1(k1_xboole_0),X1),X2)
    | r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_relat_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_relat_1(k2_zfmisc_1(X2,X3)))
    | r1_tarski(X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_25])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_19])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(k2_relat_1(k2_zfmisc_1(X1,X2)),X3),X2)
    | r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_25])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(k2_zfmisc_1(X1,X3)))
    | r1_tarski(X1,X2)
    | r1_tarski(X3,X4) ),
    inference(spm,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_2(k1_relat_1(k2_zfmisc_1(X1,X2)),X3),X1)
    | r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_40,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,plain,
    ( X2 = k1_relat_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_42,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_43,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
              & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t195_relat_1])).

cnf(c_0_44,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_38])).

cnf(c_0_46,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_39])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( X1 = k1_relat_1(X2)
    | ~ r2_hidden(esk3_2(X2,X1),k1_relat_1(X3))
    | ~ r2_hidden(esk3_2(X2,X1),X1)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_14])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_51,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    & esk9_0 != k1_xboole_0
    & ( k1_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk8_0
      | k2_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk9_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).

cnf(c_0_52,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | ~ r1_tarski(X2,k2_relat_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_44])).

cnf(c_0_53,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | r1_tarski(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_45]),c_0_46])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k2_relat_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_22])).

cnf(c_0_55,plain,
    ( X1 = k1_relat_1(X2)
    | ~ r2_hidden(esk3_2(X2,X1),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_42]),c_0_19])]),c_0_49])).

cnf(c_0_56,plain,
    ( X1 = k1_relat_1(k2_zfmisc_1(X2,X3))
    | r2_hidden(esk3_2(k2_zfmisc_1(X2,X3),X1),X1)
    | r2_hidden(esk3_2(k2_zfmisc_1(X2,X3),X1),X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_50])).

cnf(c_0_57,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk8_0
    | k2_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | k2_relat_1(k2_zfmisc_1(X3,X2)) = X2 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X3 = X2
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_53])).

cnf(c_0_61,plain,
    ( r2_hidden(esk1_2(X1,X2),k2_relat_1(k2_zfmisc_1(X3,X1)))
    | r1_tarski(X1,X2)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_25])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(k2_zfmisc_1(k1_xboole_0,X2),X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(X1,esk9_0)) = X1
    | k1_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk8_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | k1_xboole_0 = X2 ),
    inference(spm,[status(thm)],[c_0_60,c_0_19])).

cnf(c_0_65,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X2,X3),k2_relat_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(X1,esk9_0)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,k2_relat_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(esk8_0,esk9_0)) != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_67])])).

cnf(c_0_70,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X1 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_68]),c_0_44])])).

cnf(c_0_71,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 4.91/5.16  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 4.91/5.16  # and selection function SelectComplexExceptUniqMaxHorn.
% 4.91/5.16  #
% 4.91/5.16  # Preprocessing time       : 0.028 s
% 4.91/5.16  # Presaturation interreduction done
% 4.91/5.16  
% 4.91/5.16  # Proof found!
% 4.91/5.16  # SZS status Theorem
% 4.91/5.16  # SZS output start CNFRefutation
% 4.91/5.16  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 4.91/5.16  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.91/5.16  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.91/5.16  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.91/5.16  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 4.91/5.16  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.91/5.16  fof(t195_relat_1, conjecture, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 4.91/5.16  fof(c_0_7, plain, ![X18, X19, X20, X22, X23, X24, X25, X27]:(((~r2_hidden(X20,X19)|r2_hidden(k4_tarski(X20,esk2_3(X18,X19,X20)),X18)|X19!=k1_relat_1(X18))&(~r2_hidden(k4_tarski(X22,X23),X18)|r2_hidden(X22,X19)|X19!=k1_relat_1(X18)))&((~r2_hidden(esk3_2(X24,X25),X25)|~r2_hidden(k4_tarski(esk3_2(X24,X25),X27),X24)|X25=k1_relat_1(X24))&(r2_hidden(esk3_2(X24,X25),X25)|r2_hidden(k4_tarski(esk3_2(X24,X25),esk4_2(X24,X25)),X24)|X25=k1_relat_1(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 4.91/5.16  fof(c_0_8, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 4.91/5.16  cnf(c_0_9, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 4.91/5.16  fof(c_0_10, plain, ![X14, X15, X16, X17]:(((r2_hidden(X14,X16)|~r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17)))&(r2_hidden(X15,X17)|~r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17))))&(~r2_hidden(X14,X16)|~r2_hidden(X15,X17)|r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 4.91/5.16  cnf(c_0_11, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 4.91/5.16  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_9])).
% 4.91/5.16  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 4.91/5.16  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X3)|~r2_hidden(X1,k1_relat_1(X2))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 4.91/5.16  fof(c_0_15, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 4.91/5.16  fof(c_0_16, plain, ![X29, X30, X31, X33, X34, X35, X36, X38]:(((~r2_hidden(X31,X30)|r2_hidden(k4_tarski(esk5_3(X29,X30,X31),X31),X29)|X30!=k2_relat_1(X29))&(~r2_hidden(k4_tarski(X34,X33),X29)|r2_hidden(X33,X30)|X30!=k2_relat_1(X29)))&((~r2_hidden(esk6_2(X35,X36),X36)|~r2_hidden(k4_tarski(X38,esk6_2(X35,X36)),X35)|X36=k2_relat_1(X35))&(r2_hidden(esk6_2(X35,X36),X36)|r2_hidden(k4_tarski(esk7_2(X35,X36),esk6_2(X35,X36)),X35)|X36=k2_relat_1(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 4.91/5.16  cnf(c_0_17, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 4.91/5.16  cnf(c_0_18, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~r1_tarski(X3,k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 4.91/5.16  cnf(c_0_19, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.91/5.16  cnf(c_0_20, plain, (r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.91/5.16  cnf(c_0_21, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_17])).
% 4.91/5.16  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 4.91/5.16  fof(c_0_23, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 4.91/5.16  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 4.91/5.16  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 4.91/5.16  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 4.91/5.16  cnf(c_0_27, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_20])).
% 4.91/5.16  cnf(c_0_28, plain, (r2_hidden(X1,k1_relat_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X3)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 4.91/5.16  cnf(c_0_29, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.91/5.16  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 4.91/5.16  cnf(c_0_31, plain, (r2_hidden(esk1_2(k1_relat_1(k1_xboole_0),X1),X2)|r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 4.91/5.16  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k2_relat_1(k2_zfmisc_1(X3,X2)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 4.91/5.16  cnf(c_0_33, plain, (r2_hidden(X1,k1_relat_1(k2_zfmisc_1(X2,X3)))|r1_tarski(X3,X4)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_25])).
% 4.91/5.16  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_13, c_0_12])).
% 4.91/5.16  cnf(c_0_35, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_19])).
% 4.91/5.16  cnf(c_0_36, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 4.91/5.16  cnf(c_0_37, plain, (r2_hidden(esk1_2(k2_relat_1(k2_zfmisc_1(X1,X2)),X3),X2)|r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_32, c_0_25])).
% 4.91/5.16  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(k2_zfmisc_1(X1,X3)))|r1_tarski(X1,X2)|r1_tarski(X3,X4)), inference(spm,[status(thm)],[c_0_33, c_0_25])).
% 4.91/5.16  cnf(c_0_39, plain, (r2_hidden(esk1_2(k1_relat_1(k2_zfmisc_1(X1,X2)),X3),X1)|r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_34, c_0_25])).
% 4.91/5.16  cnf(c_0_40, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.91/5.16  cnf(c_0_41, plain, (X2=k1_relat_1(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(k4_tarski(esk3_2(X1,X2),X3),X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 4.91/5.16  cnf(c_0_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 4.91/5.16  fof(c_0_43, negated_conjecture, ~(![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2))))), inference(assume_negation,[status(cth)],[t195_relat_1])).
% 4.91/5.16  cnf(c_0_44, plain, (r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_30, c_0_37])).
% 4.91/5.16  cnf(c_0_45, plain, (r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X2)))|r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_30, c_0_38])).
% 4.91/5.16  cnf(c_0_46, plain, (r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_30, c_0_39])).
% 4.91/5.16  cnf(c_0_47, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_40])).
% 4.91/5.16  cnf(c_0_48, plain, (X1=k1_relat_1(X2)|~r2_hidden(esk3_2(X2,X1),k1_relat_1(X3))|~r2_hidden(esk3_2(X2,X1),X1)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_41, c_0_14])).
% 4.91/5.16  cnf(c_0_49, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_24, c_0_42])).
% 4.91/5.16  cnf(c_0_50, plain, (r2_hidden(esk3_2(X1,X2),X2)|r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 4.91/5.16  fof(c_0_51, negated_conjecture, ((esk8_0!=k1_xboole_0&esk9_0!=k1_xboole_0)&(k1_relat_1(k2_zfmisc_1(esk8_0,esk9_0))!=esk8_0|k2_relat_1(k2_zfmisc_1(esk8_0,esk9_0))!=esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).
% 4.91/5.16  cnf(c_0_52, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|~r1_tarski(X2,k2_relat_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_29, c_0_44])).
% 4.91/5.16  cnf(c_0_53, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|r1_tarski(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_45]), c_0_46])])).
% 4.91/5.16  cnf(c_0_54, plain, (r2_hidden(X1,k2_relat_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_47, c_0_22])).
% 4.91/5.16  cnf(c_0_55, plain, (X1=k1_relat_1(X2)|~r2_hidden(esk3_2(X2,X1),k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_42]), c_0_19])]), c_0_49])).
% 4.91/5.16  cnf(c_0_56, plain, (X1=k1_relat_1(k2_zfmisc_1(X2,X3))|r2_hidden(esk3_2(k2_zfmisc_1(X2,X3),X1),X1)|r2_hidden(esk3_2(k2_zfmisc_1(X2,X3),X1),X2)), inference(spm,[status(thm)],[c_0_13, c_0_50])).
% 4.91/5.16  cnf(c_0_57, plain, (k1_relat_1(k2_zfmisc_1(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_46])).
% 4.91/5.16  cnf(c_0_58, negated_conjecture, (k1_relat_1(k2_zfmisc_1(esk8_0,esk9_0))!=esk8_0|k2_relat_1(k2_zfmisc_1(esk8_0,esk9_0))!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 4.91/5.16  cnf(c_0_59, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|k2_relat_1(k2_zfmisc_1(X3,X2))=X2), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 4.91/5.16  cnf(c_0_60, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|X3=X2|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_29, c_0_53])).
% 4.91/5.16  cnf(c_0_61, plain, (r2_hidden(esk1_2(X1,X2),k2_relat_1(k2_zfmisc_1(X3,X1)))|r1_tarski(X1,X2)|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_54, c_0_25])).
% 4.91/5.16  cnf(c_0_62, plain, (X1=k1_xboole_0|r2_hidden(esk3_2(k2_zfmisc_1(k1_xboole_0,X2),X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 4.91/5.16  cnf(c_0_63, negated_conjecture, (k1_relat_1(k2_zfmisc_1(X1,esk9_0))=X1|k1_relat_1(k2_zfmisc_1(esk8_0,esk9_0))!=esk8_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 4.91/5.16  cnf(c_0_64, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|k1_xboole_0=X2), inference(spm,[status(thm)],[c_0_60, c_0_19])).
% 4.91/5.16  cnf(c_0_65, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 4.91/5.16  cnf(c_0_66, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X2,X3),k2_relat_1(k2_zfmisc_1(X1,X2)))|r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 4.91/5.16  cnf(c_0_67, negated_conjecture, (k1_relat_1(k2_zfmisc_1(X1,esk9_0))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 4.91/5.16  cnf(c_0_68, plain, (X1=k1_xboole_0|r1_tarski(X2,k2_relat_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_30, c_0_66])).
% 4.91/5.16  cnf(c_0_69, negated_conjecture, (k2_relat_1(k2_zfmisc_1(esk8_0,esk9_0))!=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_67])])).
% 4.91/5.16  cnf(c_0_70, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|X1=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_68]), c_0_44])])).
% 4.91/5.16  cnf(c_0_71, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 4.91/5.16  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), ['proof']).
% 4.91/5.16  # SZS output end CNFRefutation
% 4.91/5.16  # Proof object total steps             : 73
% 4.91/5.16  # Proof object clause steps            : 58
% 4.91/5.16  # Proof object formula steps           : 15
% 4.91/5.16  # Proof object conjectures             : 10
% 4.91/5.16  # Proof object clause conjectures      : 7
% 4.91/5.16  # Proof object formula conjectures     : 3
% 4.91/5.16  # Proof object initial clauses used    : 17
% 4.91/5.16  # Proof object initial formulas used   : 7
% 4.91/5.16  # Proof object generating inferences   : 35
% 4.91/5.16  # Proof object simplifying inferences  : 17
% 4.91/5.16  # Training examples: 0 positive, 0 negative
% 4.91/5.16  # Parsed axioms                        : 7
% 4.91/5.16  # Removed by relevancy pruning/SinE    : 0
% 4.91/5.16  # Initial clauses                      : 21
% 4.91/5.16  # Removed in clause preprocessing      : 0
% 4.91/5.16  # Initial clauses in saturation        : 21
% 4.91/5.16  # Processed clauses                    : 12827
% 4.91/5.16  # ...of these trivial                  : 7
% 4.91/5.16  # ...subsumed                          : 10961
% 4.91/5.16  # ...remaining for further processing  : 1859
% 4.91/5.16  # Other redundant clauses eliminated   : 7010
% 4.91/5.16  # Clauses deleted for lack of memory   : 0
% 4.91/5.16  # Backward-subsumed                    : 43
% 4.91/5.16  # Backward-rewritten                   : 10
% 4.91/5.16  # Generated clauses                    : 750335
% 4.91/5.16  # ...of the previous two non-trivial   : 700610
% 4.91/5.16  # Contextual simplify-reflections      : 10
% 4.91/5.16  # Paramodulations                      : 743177
% 4.91/5.16  # Factorizations                       : 148
% 4.91/5.16  # Equation resolutions                 : 7010
% 4.91/5.16  # Propositional unsat checks           : 0
% 4.91/5.16  #    Propositional check models        : 0
% 4.91/5.16  #    Propositional check unsatisfiable : 0
% 4.91/5.16  #    Propositional clauses             : 0
% 4.91/5.16  #    Propositional clauses after purity: 0
% 4.91/5.16  #    Propositional unsat core size     : 0
% 4.91/5.16  #    Propositional preprocessing time  : 0.000
% 4.91/5.16  #    Propositional encoding time       : 0.000
% 4.91/5.16  #    Propositional solver time         : 0.000
% 4.91/5.16  #    Success case prop preproc time    : 0.000
% 4.91/5.16  #    Success case prop encoding time   : 0.000
% 4.91/5.16  #    Success case prop solver time     : 0.000
% 4.91/5.16  # Current number of processed clauses  : 1780
% 4.91/5.16  #    Positive orientable unit clauses  : 24
% 4.91/5.16  #    Positive unorientable unit clauses: 0
% 4.91/5.16  #    Negative unit clauses             : 4
% 4.91/5.16  #    Non-unit-clauses                  : 1752
% 4.91/5.16  # Current number of unprocessed clauses: 687125
% 4.91/5.16  # ...number of literals in the above   : 2702172
% 4.91/5.16  # Current number of archived formulas  : 0
% 4.91/5.16  # Current number of archived clauses   : 73
% 4.91/5.16  # Clause-clause subsumption calls (NU) : 1400784
% 4.91/5.16  # Rec. Clause-clause subsumption calls : 852186
% 4.91/5.16  # Non-unit clause-clause subsumptions  : 11009
% 4.91/5.16  # Unit Clause-clause subsumption calls : 6664
% 4.91/5.16  # Rewrite failures with RHS unbound    : 0
% 4.91/5.16  # BW rewrite match attempts            : 139
% 4.91/5.16  # BW rewrite match successes           : 7
% 4.91/5.16  # Condensation attempts                : 0
% 4.91/5.16  # Condensation successes               : 0
% 4.91/5.16  # Termbank termtop insertions          : 15503954
% 5.01/5.18  
% 5.01/5.18  # -------------------------------------------------
% 5.01/5.18  # User time                : 4.578 s
% 5.01/5.18  # System time              : 0.258 s
% 5.01/5.18  # Total time               : 4.835 s
% 5.01/5.18  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
