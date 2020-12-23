%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:12 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 572 expanded)
%              Number of clauses        :   64 ( 294 expanded)
%              Number of leaves         :    9 ( 135 expanded)
%              Depth                    :   20
%              Number of atoms          :  207 (1576 expanded)
%              Number of equality atoms :   80 ( 696 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
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

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t8_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

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

fof(c_0_9,plain,(
    ! [X20,X21] :
      ( ( ~ r1_tarski(X20,k1_tarski(X21))
        | X20 = k1_xboole_0
        | X20 = k1_tarski(X21) )
      & ( X20 != k1_xboole_0
        | r1_tarski(X20,k1_tarski(X21)) )
      & ( X20 != k1_tarski(X21)
        | r1_tarski(X20,k1_tarski(X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_10,plain,(
    ! [X19] : k2_tarski(X19,X19) = k1_tarski(X19) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X14,X13)
        | X14 = X12
        | X13 != k1_tarski(X12) )
      & ( X15 != X12
        | r2_hidden(X15,X13)
        | X13 != k1_tarski(X12) )
      & ( ~ r2_hidden(esk2_2(X16,X17),X17)
        | esk2_2(X16,X17) != X16
        | X17 = k1_tarski(X16) )
      & ( r2_hidden(esk2_2(X16,X17),X17)
        | esk2_2(X16,X17) = X16
        | X17 = k1_tarski(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k2_tarski(X2,X2))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[c_0_16])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

cnf(c_0_21,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k2_tarski(X2,X2))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_23,plain,(
    ! [X22,X23,X24] :
      ( ( r2_hidden(X22,X23)
        | ~ r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))) )
      & ( X22 != X24
        | ~ r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))) )
      & ( ~ r2_hidden(X22,X23)
        | X22 = X24
        | r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_24,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk4_0)) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_25,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk4_0)) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( esk1_2(k1_xboole_0,X1) = X2
    | r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_30,plain,(
    ! [X28,X29,X30] :
      ( ~ r2_hidden(X28,X29)
      | ~ r1_tarski(X28,X30)
      | r1_tarski(k1_setfam_1(X29),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).

fof(c_0_31,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X3,X3))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,esk4_0)) != esk4_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_13])).

cnf(c_0_34,plain,
    ( X1 = X2
    | r1_tarski(k1_xboole_0,X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_setfam_1(X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,k2_tarski(X2,X2)),X3),X1)
    | r1_tarski(k4_xboole_0(X1,k2_tarski(X2,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_26])).

cnf(c_0_40,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_43,plain,
    ( esk1_2(k2_tarski(X1,X1),X2) = X1
    | r1_tarski(k2_tarski(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_26])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_setfam_1(X1),X2)
    | r1_tarski(X1,X3)
    | ~ r1_tarski(esk1_2(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_26])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_tarski(X2,X2)
    | ~ r1_tarski(X1,k2_tarski(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_13]),c_0_13])).

cnf(c_0_48,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_tarski(X2,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( r1_tarski(k2_tarski(X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_43])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_13])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_setfam_1(X1),esk1_2(X1,X2))
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_55,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)) = k2_tarski(X1,X1)
    | k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1))) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k2_tarski(X1,X1) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_42])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X1)),X1)
    | r1_tarski(k2_tarski(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_43])).

cnf(c_0_61,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X3,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_54,c_0_13])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)) = k1_xboole_0
    | k2_tarski(X1,X1) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X1)),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_59])).

cnf(c_0_65,plain,
    ( k2_tarski(X1,X1) = k2_tarski(X2,X2)
    | k2_tarski(X1,X1) = k1_xboole_0
    | r1_tarski(k1_setfam_1(k2_tarski(X1,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_60])).

cnf(c_0_66,plain,
    ( X1 = X2
    | k2_tarski(X3,X3) != k1_xboole_0
    | ~ r2_hidden(X1,k2_tarski(X3,X3)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,X1)) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_64])).

cnf(c_0_68,plain,
    ( k2_tarski(X1,X1) = k1_xboole_0
    | r2_hidden(X2,k2_tarski(X1,X1))
    | r1_tarski(k1_setfam_1(k2_tarski(X1,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_65])).

cnf(c_0_69,plain,
    ( X1 = X2
    | k2_tarski(X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_67]),c_0_50])).

cnf(c_0_71,plain,
    ( X1 = X2
    | r1_tarski(k1_setfam_1(k2_tarski(X2,X2)),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_68]),c_0_69])).

fof(c_0_72,plain,(
    ! [X25,X26] :
      ( ( r2_hidden(esk3_2(X25,X26),X25)
        | X25 = k1_xboole_0
        | r1_tarski(X26,k1_setfam_1(X25)) )
      & ( ~ r1_tarski(X26,esk3_2(X25,X26))
        | X25 = k1_xboole_0
        | r1_tarski(X26,k1_setfam_1(X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k2_tarski(esk4_0,esk4_0)),esk4_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k2_tarski(esk4_0,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_48])).

cnf(c_0_76,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk3_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_77,plain,
    ( esk3_2(k2_tarski(X1,X1),X2) = X1
    | k2_tarski(X1,X1) = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(k2_tarski(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_75]),c_0_33])).

cnf(c_0_79,plain,
    ( k2_tarski(X1,X1) = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(k2_tarski(X1,X1)))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( k2_tarski(esk4_0,esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_46])])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_57]),c_0_25])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_80]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:03:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.027 s
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.20/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.41  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.41  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.20/0.41  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.20/0.41  fof(t8_setfam_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_setfam_1)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 0.20/0.41  fof(c_0_9, plain, ![X20, X21]:((~r1_tarski(X20,k1_tarski(X21))|(X20=k1_xboole_0|X20=k1_tarski(X21)))&((X20!=k1_xboole_0|r1_tarski(X20,k1_tarski(X21)))&(X20!=k1_tarski(X21)|r1_tarski(X20,k1_tarski(X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.20/0.41  fof(c_0_10, plain, ![X19]:k2_tarski(X19,X19)=k1_tarski(X19), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.41  fof(c_0_11, plain, ![X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X14,X13)|X14=X12|X13!=k1_tarski(X12))&(X15!=X12|r2_hidden(X15,X13)|X13!=k1_tarski(X12)))&((~r2_hidden(esk2_2(X16,X17),X17)|esk2_2(X16,X17)!=X16|X17=k1_tarski(X16))&(r2_hidden(esk2_2(X16,X17),X17)|esk2_2(X16,X17)=X16|X17=k1_tarski(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.41  cnf(c_0_12, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_13, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_14, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  fof(c_0_15, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.41  cnf(c_0_16, plain, (r1_tarski(X1,k2_tarski(X2,X2))|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.41  cnf(c_0_17, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_13])).
% 0.20/0.41  cnf(c_0_18, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_19, plain, (r1_tarski(k1_xboole_0,k2_tarski(X1,X1))), inference(er,[status(thm)],[c_0_16])).
% 0.20/0.41  fof(c_0_20, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 0.20/0.41  cnf(c_0_21, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_22, plain, (r2_hidden(X1,k2_tarski(X2,X2))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.41  fof(c_0_23, plain, ![X22, X23, X24]:(((r2_hidden(X22,X23)|~r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))))&(X22!=X24|~r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24)))))&(~r2_hidden(X22,X23)|X22=X24|r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.20/0.41  fof(c_0_24, negated_conjecture, k1_setfam_1(k1_tarski(esk4_0))!=esk4_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.20/0.41  cnf(c_0_25, plain, (X1=X2|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.41  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_27, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (k1_setfam_1(k1_tarski(esk4_0))!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  cnf(c_0_29, plain, (esk1_2(k1_xboole_0,X1)=X2|r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.41  fof(c_0_30, plain, ![X28, X29, X30]:(~r2_hidden(X28,X29)|~r1_tarski(X28,X30)|r1_tarski(k1_setfam_1(X29),X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).
% 0.20/0.41  fof(c_0_31, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X3,X3)))), inference(rw,[status(thm)],[c_0_27, c_0_13])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,esk4_0))!=esk4_0), inference(rw,[status(thm)],[c_0_28, c_0_13])).
% 0.20/0.41  cnf(c_0_34, plain, (X1=X2|r1_tarski(k1_xboole_0,X3)), inference(spm,[status(thm)],[c_0_29, c_0_29])).
% 0.20/0.41  cnf(c_0_35, plain, (r1_tarski(k1_setfam_1(X2),X3)|~r2_hidden(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.41  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_37, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_39, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,k2_tarski(X2,X2)),X3),X1)|r1_tarski(k4_xboole_0(X1,k2_tarski(X2,X2)),X3)), inference(spm,[status(thm)],[c_0_32, c_0_26])).
% 0.20/0.41  cnf(c_0_40, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_41, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (r1_tarski(k1_xboole_0,X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34])])).
% 0.20/0.41  cnf(c_0_43, plain, (esk1_2(k2_tarski(X1,X1),X2)=X1|r1_tarski(k2_tarski(X1,X1),X2)), inference(spm,[status(thm)],[c_0_21, c_0_26])).
% 0.20/0.41  cnf(c_0_44, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_45, plain, (r1_tarski(k1_setfam_1(X1),X2)|r1_tarski(X1,X3)|~r1_tarski(esk1_2(X1,X3),X2)), inference(spm,[status(thm)],[c_0_35, c_0_26])).
% 0.20/0.41  cnf(c_0_46, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36])).
% 0.20/0.41  cnf(c_0_47, plain, (X1=k1_xboole_0|X1=k2_tarski(X2,X2)|~r1_tarski(X1,k2_tarski(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_13]), c_0_13])).
% 0.20/0.41  cnf(c_0_48, plain, (r1_tarski(k4_xboole_0(X1,k2_tarski(X2,X2)),X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.41  cnf(c_0_49, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2)))), inference(rw,[status(thm)],[c_0_40, c_0_13])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.41  cnf(c_0_51, plain, (r1_tarski(k2_tarski(X1,X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_43])).
% 0.20/0.41  cnf(c_0_52, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_44, c_0_13])).
% 0.20/0.41  cnf(c_0_53, plain, (r1_tarski(k1_setfam_1(X1),esk1_2(X1,X2))|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.41  cnf(c_0_54, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_55, plain, (k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))=k2_tarski(X1,X1)|k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.41  cnf(c_0_56, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1)))), inference(er,[status(thm)],[c_0_49])).
% 0.20/0.41  cnf(c_0_57, negated_conjecture, (k2_tarski(X1,X1)=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_42])).
% 0.20/0.41  cnf(c_0_59, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).
% 0.20/0.41  cnf(c_0_60, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X1)),X1)|r1_tarski(k2_tarski(X1,X1),X2)), inference(spm,[status(thm)],[c_0_53, c_0_43])).
% 0.20/0.41  cnf(c_0_61, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X3,X3)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_54, c_0_13])).
% 0.20/0.41  cnf(c_0_62, plain, (k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))=k1_xboole_0|k2_tarski(X1,X1)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_55])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.20/0.41  cnf(c_0_64, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X1)),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_59])).
% 0.20/0.41  cnf(c_0_65, plain, (k2_tarski(X1,X1)=k2_tarski(X2,X2)|k2_tarski(X1,X1)=k1_xboole_0|r1_tarski(k1_setfam_1(k2_tarski(X1,X1)),X1)), inference(spm,[status(thm)],[c_0_47, c_0_60])).
% 0.20/0.41  cnf(c_0_66, plain, (X1=X2|k2_tarski(X3,X3)!=k1_xboole_0|~r2_hidden(X1,k2_tarski(X3,X3))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (k1_setfam_1(k2_tarski(X1,X1))=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_64])).
% 0.20/0.41  cnf(c_0_68, plain, (k2_tarski(X1,X1)=k1_xboole_0|r2_hidden(X2,k2_tarski(X1,X1))|r1_tarski(k1_setfam_1(k2_tarski(X1,X1)),X1)), inference(spm,[status(thm)],[c_0_59, c_0_65])).
% 0.20/0.41  cnf(c_0_69, plain, (X1=X2|k2_tarski(X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_59])).
% 0.20/0.41  cnf(c_0_70, negated_conjecture, (~r1_tarski(esk4_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_67]), c_0_50])).
% 0.20/0.41  cnf(c_0_71, plain, (X1=X2|r1_tarski(k1_setfam_1(k2_tarski(X2,X2)),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_68]), c_0_69])).
% 0.20/0.41  fof(c_0_72, plain, ![X25, X26]:((r2_hidden(esk3_2(X25,X26),X25)|(X25=k1_xboole_0|r1_tarski(X26,k1_setfam_1(X25))))&(~r1_tarski(X26,esk3_2(X25,X26))|(X25=k1_xboole_0|r1_tarski(X26,k1_setfam_1(X25))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (r1_tarski(k1_setfam_1(k2_tarski(esk4_0,esk4_0)),esk4_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.41  cnf(c_0_74, plain, (r2_hidden(esk3_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (r1_tarski(k1_setfam_1(k2_tarski(esk4_0,esk4_0)),esk4_0)), inference(spm,[status(thm)],[c_0_73, c_0_48])).
% 0.20/0.41  cnf(c_0_76, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk3_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.42  cnf(c_0_77, plain, (esk3_2(k2_tarski(X1,X1),X2)=X1|k2_tarski(X1,X1)=k1_xboole_0|r1_tarski(X2,k1_setfam_1(k2_tarski(X1,X1)))), inference(spm,[status(thm)],[c_0_21, c_0_74])).
% 0.20/0.42  cnf(c_0_78, negated_conjecture, (~r1_tarski(esk4_0,k1_setfam_1(k2_tarski(esk4_0,esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_75]), c_0_33])).
% 0.20/0.42  cnf(c_0_79, plain, (k2_tarski(X1,X1)=k1_xboole_0|r1_tarski(X2,k1_setfam_1(k2_tarski(X1,X1)))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.42  cnf(c_0_80, negated_conjecture, (k2_tarski(esk4_0,esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_46])])).
% 0.20/0.42  cnf(c_0_81, negated_conjecture, (~r2_hidden(esk4_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_57]), c_0_25])).
% 0.20/0.42  cnf(c_0_82, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_80]), c_0_81]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 83
% 0.20/0.42  # Proof object clause steps            : 64
% 0.20/0.42  # Proof object formula steps           : 19
% 0.20/0.42  # Proof object conjectures             : 18
% 0.20/0.42  # Proof object clause conjectures      : 15
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 17
% 0.20/0.42  # Proof object initial formulas used   : 9
% 0.20/0.42  # Proof object generating inferences   : 34
% 0.20/0.42  # Proof object simplifying inferences  : 25
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 9
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 21
% 0.20/0.42  # Removed in clause preprocessing      : 1
% 0.20/0.42  # Initial clauses in saturation        : 20
% 0.20/0.42  # Processed clauses                    : 140
% 0.20/0.42  # ...of these trivial                  : 6
% 0.20/0.42  # ...subsumed                          : 36
% 0.20/0.42  # ...remaining for further processing  : 98
% 0.20/0.42  # Other redundant clauses eliminated   : 122
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 9
% 0.20/0.42  # Backward-rewritten                   : 12
% 0.20/0.42  # Generated clauses                    : 2022
% 0.20/0.42  # ...of the previous two non-trivial   : 1656
% 0.20/0.42  # Contextual simplify-reflections      : 6
% 0.20/0.42  # Paramodulations                      : 1889
% 0.20/0.42  # Factorizations                       : 12
% 0.20/0.42  # Equation resolutions                 : 122
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 70
% 0.20/0.42  #    Positive orientable unit clauses  : 8
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 4
% 0.20/0.42  #    Non-unit-clauses                  : 58
% 0.20/0.42  # Current number of unprocessed clauses: 1404
% 0.20/0.42  # ...number of literals in the above   : 7335
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 22
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 357
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 270
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 27
% 0.20/0.42  # Unit Clause-clause subsumption calls : 47
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 11
% 0.20/0.42  # BW rewrite match successes           : 8
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 27274
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.066 s
% 0.20/0.42  # System time              : 0.006 s
% 0.20/0.42  # Total time               : 0.073 s
% 0.20/0.42  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
