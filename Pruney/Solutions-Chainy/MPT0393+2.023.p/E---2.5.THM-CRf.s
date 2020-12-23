%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:12 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 373 expanded)
%              Number of clauses        :   51 ( 176 expanded)
%              Number of leaves         :   12 (  98 expanded)
%              Depth                    :   16
%              Number of atoms          :  206 ( 919 expanded)
%              Number of equality atoms :   97 ( 487 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(c_0_12,plain,(
    ! [X35,X36] :
      ( ( ~ r1_tarski(X35,k1_tarski(X36))
        | X35 = k1_xboole_0
        | X35 = k1_tarski(X36) )
      & ( X35 != k1_xboole_0
        | r1_tarski(X35,k1_tarski(X36)) )
      & ( X35 != k1_tarski(X36)
        | r1_tarski(X35,k1_tarski(X36)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_13,plain,(
    ! [X29] : k2_tarski(X29,X29) = k1_tarski(X29) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X30,X31] : k1_enumset1(X30,X30,X31) = k2_tarski(X30,X31) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X32,X33,X34] : k2_enumset1(X32,X32,X33,X34) = k1_enumset1(X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X13
        | X14 != k1_tarski(X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_tarski(X13) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) != X17
        | X18 = k1_tarski(X17) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) = X17
        | X18 = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_17,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X37,X38,X39] :
      ( ( r2_hidden(X37,X38)
        | ~ r2_hidden(X37,k4_xboole_0(X38,k1_tarski(X39))) )
      & ( X37 != X39
        | ~ r2_hidden(X37,k4_xboole_0(X38,k1_tarski(X39))) )
      & ( ~ r2_hidden(X37,X38)
        | X37 = X39
        | r2_hidden(X37,k4_xboole_0(X38,k1_tarski(X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

cnf(c_0_23,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_26,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))
    | X3 != k1_xboole_0
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_30,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X23,X22)
        | X23 = X20
        | X23 = X21
        | X22 != k2_tarski(X20,X21) )
      & ( X24 != X20
        | r2_hidden(X24,X22)
        | X22 != k2_tarski(X20,X21) )
      & ( X24 != X21
        | r2_hidden(X24,X22)
        | X22 != k2_tarski(X20,X21) )
      & ( esk3_3(X25,X26,X27) != X25
        | ~ r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k2_tarski(X25,X26) )
      & ( esk3_3(X25,X26,X27) != X26
        | ~ r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k2_tarski(X25,X26) )
      & ( r2_hidden(esk3_3(X25,X26,X27),X27)
        | esk3_3(X25,X26,X27) = X25
        | esk3_3(X25,X26,X27) = X26
        | X27 = k2_tarski(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_2(X1,X2),k2_enumset1(X3,X3,X3,X3))
    | r1_tarski(X1,X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( esk1_2(X1,X2) = X3
    | r1_tarski(X1,X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_20]),c_0_21])).

fof(c_0_40,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3),X1)
    | r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_29])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X1 != k1_xboole_0
    | ~ r2_hidden(X3,esk1_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X3,X3,X1) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | X1 != k1_xboole_0
    | ~ r2_hidden(X3,X4) ),
    inference(spm,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)) = X1
    | ~ r1_tarski(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_20]),c_0_21])).

fof(c_0_53,plain,(
    ! [X42,X43] :
      ( ( r2_hidden(esk4_2(X42,X43),X42)
        | X42 = k1_xboole_0
        | r1_tarski(X43,k1_setfam_1(X42)) )
      & ( ~ r1_tarski(X43,esk4_2(X42,X43))
        | X42 = k1_xboole_0
        | r1_tarski(X43,k1_setfam_1(X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)) = X1
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_55,plain,(
    ! [X40,X41] :
      ( ~ r2_hidden(X40,X41)
      | r1_tarski(k1_setfam_1(X41),X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X1,X1,X1,X3) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_57,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_54])).

fof(c_0_59,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_62,plain,
    ( esk4_2(k2_enumset1(X1,X1,X1,X1),X2) = X1
    | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_57])).

cnf(c_0_63,plain,
    ( k2_enumset1(X1,X1,X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_48])).

fof(c_0_64,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk5_0)) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_59])])])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk4_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_67,plain,
    ( esk4_2(k2_enumset1(X1,X1,X1,X1),X2) = X1
    | r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))) ),
    inference(sr,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_69,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk5_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_65])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_63])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_74,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 19:58:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.20/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.20/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 0.20/0.38  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.20/0.38  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.20/0.38  fof(c_0_12, plain, ![X35, X36]:((~r1_tarski(X35,k1_tarski(X36))|(X35=k1_xboole_0|X35=k1_tarski(X36)))&((X35!=k1_xboole_0|r1_tarski(X35,k1_tarski(X36)))&(X35!=k1_tarski(X36)|r1_tarski(X35,k1_tarski(X36))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.20/0.38  fof(c_0_13, plain, ![X29]:k2_tarski(X29,X29)=k1_tarski(X29), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.38  fof(c_0_14, plain, ![X30, X31]:k1_enumset1(X30,X30,X31)=k2_tarski(X30,X31), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_15, plain, ![X32, X33, X34]:k2_enumset1(X32,X32,X33,X34)=k1_enumset1(X32,X33,X34), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.38  fof(c_0_16, plain, ![X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X15,X14)|X15=X13|X14!=k1_tarski(X13))&(X16!=X13|r2_hidden(X16,X14)|X14!=k1_tarski(X13)))&((~r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)!=X17|X18=k1_tarski(X17))&(r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)=X17|X18=k1_tarski(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.38  fof(c_0_17, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_18, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  fof(c_0_22, plain, ![X37, X38, X39]:(((r2_hidden(X37,X38)|~r2_hidden(X37,k4_xboole_0(X38,k1_tarski(X39))))&(X37!=X39|~r2_hidden(X37,k4_xboole_0(X38,k1_tarski(X39)))))&(~r2_hidden(X37,X38)|X37=X39|r2_hidden(X37,k4_xboole_0(X38,k1_tarski(X39))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.20/0.38  cnf(c_0_23, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_24, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_25, plain, (r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])).
% 0.20/0.38  cnf(c_0_26, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_27, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_19]), c_0_20]), c_0_21])).
% 0.20/0.38  cnf(c_0_28, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))|X3!=k1_xboole_0|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.38  cnf(c_0_29, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  fof(c_0_30, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X23,X22)|(X23=X20|X23=X21)|X22!=k2_tarski(X20,X21))&((X24!=X20|r2_hidden(X24,X22)|X22!=k2_tarski(X20,X21))&(X24!=X21|r2_hidden(X24,X22)|X22!=k2_tarski(X20,X21))))&(((esk3_3(X25,X26,X27)!=X25|~r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k2_tarski(X25,X26))&(esk3_3(X25,X26,X27)!=X26|~r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k2_tarski(X25,X26)))&(r2_hidden(esk3_3(X25,X26,X27),X27)|(esk3_3(X25,X26,X27)=X25|esk3_3(X25,X26,X27)=X26)|X27=k2_tarski(X25,X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_31, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_32, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_19]), c_0_20]), c_0_21])).
% 0.20/0.38  cnf(c_0_33, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_34, plain, (r2_hidden(esk1_2(X1,X2),k2_enumset1(X3,X3,X3,X3))|r1_tarski(X1,X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.39  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_19]), c_0_20]), c_0_21])).
% 0.20/0.39  cnf(c_0_37, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))), inference(er,[status(thm)],[c_0_32])).
% 0.20/0.39  cnf(c_0_38, plain, (esk1_2(X1,X2)=X3|r1_tarski(X1,X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.39  cnf(c_0_39, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_20]), c_0_21])).
% 0.20/0.39  fof(c_0_40, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.39  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_42, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3),X1)|r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3)), inference(spm,[status(thm)],[c_0_36, c_0_29])).
% 0.20/0.39  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X1!=k1_xboole_0|~r2_hidden(X3,esk1_2(X1,X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.39  cnf(c_0_44, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X3,X3,X1)), inference(er,[status(thm)],[c_0_39])).
% 0.20/0.39  cnf(c_0_45, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.39  cnf(c_0_46, plain, (r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.39  cnf(c_0_47, plain, (r1_tarski(X1,X2)|X1!=k1_xboole_0|~r2_hidden(X3,X4)), inference(spm,[status(thm)],[c_0_43, c_0_38])).
% 0.20/0.39  cnf(c_0_48, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[c_0_44])).
% 0.20/0.39  cnf(c_0_49, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_50, plain, (k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))=X1|~r1_tarski(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.39  cnf(c_0_51, plain, (r1_tarski(X1,X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.39  cnf(c_0_52, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_20]), c_0_21])).
% 0.20/0.39  fof(c_0_53, plain, ![X42, X43]:((r2_hidden(esk4_2(X42,X43),X42)|(X42=k1_xboole_0|r1_tarski(X43,k1_setfam_1(X42))))&(~r1_tarski(X43,esk4_2(X42,X43))|(X42=k1_xboole_0|r1_tarski(X43,k1_setfam_1(X42))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 0.20/0.39  cnf(c_0_54, plain, (k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))=X1|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.39  fof(c_0_55, plain, ![X40, X41]:(~r2_hidden(X40,X41)|r1_tarski(k1_setfam_1(X41),X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.20/0.39  cnf(c_0_56, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X1,X1,X1,X3)), inference(er,[status(thm)],[c_0_52])).
% 0.20/0.39  cnf(c_0_57, plain, (r2_hidden(esk4_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.39  cnf(c_0_58, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_37, c_0_54])).
% 0.20/0.39  fof(c_0_59, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 0.20/0.39  cnf(c_0_60, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.39  cnf(c_0_61, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_56])).
% 0.20/0.39  cnf(c_0_62, plain, (esk4_2(k2_enumset1(X1,X1,X1,X1),X2)=X1|k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_33, c_0_57])).
% 0.20/0.39  cnf(c_0_63, plain, (k2_enumset1(X1,X1,X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_48])).
% 0.20/0.39  fof(c_0_64, negated_conjecture, k1_setfam_1(k1_tarski(esk5_0))!=esk5_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_59])])])).
% 0.20/0.39  cnf(c_0_65, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.39  cnf(c_0_66, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk4_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.39  cnf(c_0_67, plain, (esk4_2(k2_enumset1(X1,X1,X1,X1),X2)=X1|r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))), inference(sr,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.39  cnf(c_0_68, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (k1_setfam_1(k1_tarski(esk5_0))!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.39  cnf(c_0_70, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X1|~r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_45, c_0_65])).
% 0.20/0.39  cnf(c_0_71, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X2)))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_63])).
% 0.20/0.39  cnf(c_0_72, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_68])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_19]), c_0_20]), c_0_21])).
% 0.20/0.39  cnf(c_0_74, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])])).
% 0.20/0.39  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 76
% 0.20/0.39  # Proof object clause steps            : 51
% 0.20/0.39  # Proof object formula steps           : 25
% 0.20/0.39  # Proof object conjectures             : 6
% 0.20/0.39  # Proof object clause conjectures      : 3
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 18
% 0.20/0.39  # Proof object initial formulas used   : 12
% 0.20/0.39  # Proof object generating inferences   : 20
% 0.20/0.39  # Proof object simplifying inferences  : 29
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 12
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 29
% 0.20/0.39  # Removed in clause preprocessing      : 3
% 0.20/0.39  # Initial clauses in saturation        : 26
% 0.20/0.39  # Processed clauses                    : 219
% 0.20/0.39  # ...of these trivial                  : 14
% 0.20/0.39  # ...subsumed                          : 57
% 0.20/0.39  # ...remaining for further processing  : 148
% 0.20/0.39  # Other redundant clauses eliminated   : 6
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 13
% 0.20/0.39  # Backward-rewritten                   : 4
% 0.20/0.39  # Generated clauses                    : 833
% 0.20/0.39  # ...of the previous two non-trivial   : 700
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 817
% 0.20/0.39  # Factorizations                       : 2
% 0.20/0.39  # Equation resolutions                 : 13
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 100
% 0.20/0.39  #    Positive orientable unit clauses  : 14
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 4
% 0.20/0.39  #    Non-unit-clauses                  : 82
% 0.20/0.39  # Current number of unprocessed clauses: 506
% 0.20/0.39  # ...number of literals in the above   : 1868
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 45
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 975
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 751
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 57
% 0.20/0.39  # Unit Clause-clause subsumption calls : 90
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 25
% 0.20/0.39  # BW rewrite match successes           : 4
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 11529
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.045 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.050 s
% 0.20/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
