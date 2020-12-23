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
% DateTime   : Thu Dec  3 10:47:11 EST 2020

% Result     : Theorem 1.22s
% Output     : CNFRefutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  104 (4461 expanded)
%              Number of clauses        :   75 (2140 expanded)
%              Number of leaves         :   14 (1159 expanded)
%              Depth                    :   24
%              Number of atoms          :  269 (12722 expanded)
%              Number of equality atoms :  116 (6846 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(t5_setfam_1,axiom,(
    ! [X1] :
      ( r2_hidden(k1_xboole_0,X1)
     => k1_setfam_1(X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t8_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(c_0_14,plain,(
    ! [X46,X47,X48] :
      ( ( r2_hidden(X46,X47)
        | ~ r2_hidden(X46,k4_xboole_0(X47,k1_tarski(X48))) )
      & ( X46 != X48
        | ~ r2_hidden(X46,k4_xboole_0(X47,k1_tarski(X48))) )
      & ( ~ r2_hidden(X46,X47)
        | X46 = X48
        | r2_hidden(X46,k4_xboole_0(X47,k1_tarski(X48))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_15,plain,(
    ! [X25] : k2_tarski(X25,X25) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X18,X17)
        | X18 = X14
        | X18 = X15
        | X18 = X16
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( X19 != X14
        | r2_hidden(X19,X17)
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( X19 != X15
        | r2_hidden(X19,X17)
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( X19 != X16
        | r2_hidden(X19,X17)
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( esk2_4(X20,X21,X22,X23) != X20
        | ~ r2_hidden(esk2_4(X20,X21,X22,X23),X23)
        | X23 = k1_enumset1(X20,X21,X22) )
      & ( esk2_4(X20,X21,X22,X23) != X21
        | ~ r2_hidden(esk2_4(X20,X21,X22,X23),X23)
        | X23 = k1_enumset1(X20,X21,X22) )
      & ( esk2_4(X20,X21,X22,X23) != X22
        | ~ r2_hidden(esk2_4(X20,X21,X22,X23),X23)
        | X23 = k1_enumset1(X20,X21,X22) )
      & ( r2_hidden(esk2_4(X20,X21,X22,X23),X23)
        | esk2_4(X20,X21,X22,X23) = X20
        | esk2_4(X20,X21,X22,X23) = X21
        | esk2_4(X20,X21,X22,X23) = X22
        | X23 = k1_enumset1(X20,X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_19,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X44,X45] :
      ( ( k4_xboole_0(k1_tarski(X44),k1_tarski(X45)) != k1_tarski(X44)
        | X44 != X45 )
      & ( X44 = X45
        | k4_xboole_0(k1_tarski(X44),k1_tarski(X45)) = k1_tarski(X44) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_27,plain,
    ( X1 = X2
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( X1 = X2
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_20]),c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_22])).

fof(c_0_32,plain,(
    ! [X31,X32,X33,X35,X36,X37,X38,X40] :
      ( ( r2_hidden(X33,esk3_3(X31,X32,X33))
        | ~ r2_hidden(X33,X32)
        | X32 != k3_tarski(X31) )
      & ( r2_hidden(esk3_3(X31,X32,X33),X31)
        | ~ r2_hidden(X33,X32)
        | X32 != k3_tarski(X31) )
      & ( ~ r2_hidden(X35,X36)
        | ~ r2_hidden(X36,X31)
        | r2_hidden(X35,X32)
        | X32 != k3_tarski(X31) )
      & ( ~ r2_hidden(esk4_2(X37,X38),X38)
        | ~ r2_hidden(esk4_2(X37,X38),X40)
        | ~ r2_hidden(X40,X37)
        | X38 = k3_tarski(X37) )
      & ( r2_hidden(esk4_2(X37,X38),esk5_2(X37,X38))
        | r2_hidden(esk4_2(X37,X38),X38)
        | X38 = k3_tarski(X37) )
      & ( r2_hidden(esk5_2(X37,X38),X37)
        | r2_hidden(esk4_2(X37,X38),X38)
        | X38 = k3_tarski(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_33,plain,(
    ! [X51,X52] :
      ( ~ r2_hidden(X51,X52)
      | r1_tarski(k1_setfam_1(X52),X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X53] :
      ( ~ r2_hidden(k1_xboole_0,X53)
      | k1_setfam_1(X53) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_setfam_1])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X1,X1,X3,X4) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r2_hidden(X2,k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k1_setfam_1(X1) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_44,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( esk3_3(k2_enumset1(X1,X1,X1,X1),X2,X3) = X1
    | X2 != k3_tarski(k2_enumset1(X1,X1,X1,X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_47,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,plain,
    ( k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_51,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | X3 != k3_tarski(k2_enumset1(X2,X2,X2,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3),X1)
    | r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_tarski(k2_enumset1(X2,X2,X2,X2))) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_2(k3_tarski(k2_enumset1(X1,X1,X1,X1)),X2),X1)
    | r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_51])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,plain,
    ( r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_60])).

fof(c_0_63,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

fof(c_0_64,plain,(
    ! [X57,X58,X59] :
      ( ~ r2_hidden(X57,X58)
      | ~ r1_tarski(X57,X59)
      | r1_tarski(k1_setfam_1(X58),X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_61])).

cnf(c_0_66,plain,
    ( r2_hidden(esk3_3(k3_tarski(k2_enumset1(X1,X1,X1,X1)),X2,X3),X1)
    | X2 != k3_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_38])).

cnf(c_0_67,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_62])).

fof(c_0_68,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk7_0)) != esk7_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_63])])])).

cnf(c_0_69,plain,
    ( r1_tarski(k1_setfam_1(X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,plain,
    ( X1 != k3_tarski(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk7_0)) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X4)
    | ~ r1_tarski(X3,X4) ),
    inference(spm,[status(thm)],[c_0_69,c_0_40])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | X1 != k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_51])).

cnf(c_0_74,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) != esk7_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_75,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X2,X3)) = k1_xboole_0
    | ~ r1_tarski(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_72])).

fof(c_0_76,plain,(
    ! [X54,X55] :
      ( ( r2_hidden(esk6_2(X54,X55),X54)
        | X54 = k1_xboole_0
        | r1_tarski(X55,k1_setfam_1(X54)) )
      & ( ~ r1_tarski(X55,esk6_2(X54,X55))
        | X54 = k1_xboole_0
        | r1_tarski(X55,k1_setfam_1(X54)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | X1 != k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_tarski(esk7_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_58])).

cnf(c_0_79,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_80,plain,
    ( k2_enumset1(X1,X1,X2,X3) != k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_40])).

cnf(c_0_81,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( esk7_0 != k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_73])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0
    | r2_hidden(esk6_2(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3),X1)
    | r1_tarski(X3,k1_setfam_1(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_79])).

cnf(c_0_84,plain,
    ( k2_enumset1(X1,X1,X2,X3) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_82,c_0_81])).

cnf(c_0_86,plain,
    ( X1 = X2
    | r2_hidden(esk6_2(k2_enumset1(X1,X1,X1,X1),X3),k2_enumset1(X1,X1,X1,X1))
    | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_31]),c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk6_2(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),X1),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)))
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk6_2(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),X1),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))) ),
    inference(er,[status(thm)],[c_0_87])).

cnf(c_0_89,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r2_hidden(esk4_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)),esk6_2(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),X1))
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_88])).

cnf(c_0_91,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_89]),c_0_81])).

cnf(c_0_92,negated_conjecture,
    ( esk6_2(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),X1) = k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)))
    | ~ r1_tarski(esk6_2(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),X1),k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_90])).

cnf(c_0_93,plain,
    ( esk6_2(k2_enumset1(X1,X1,X1,X1),X2) = X1
    | r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_79]),c_0_84])).

cnf(c_0_94,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk6_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_96,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X1),esk4_2(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)))
    | ~ r1_tarski(esk7_0,k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_74])).

cnf(c_0_98,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_93]),c_0_84])).

cnf(c_0_99,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_95])).

cnf(c_0_100,plain,
    ( esk4_2(k1_xboole_0,X1) = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r1_tarski(esk4_2(k1_xboole_0,X1),k1_setfam_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(X1,k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])])).

cnf(c_0_102,plain,
    ( esk4_2(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_91]),c_0_84])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102]),c_0_74]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:48:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 1.22/1.42  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 1.22/1.42  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.22/1.42  #
% 1.22/1.42  # Preprocessing time       : 0.028 s
% 1.22/1.42  # Presaturation interreduction done
% 1.22/1.42  
% 1.22/1.42  # Proof found!
% 1.22/1.42  # SZS status Theorem
% 1.22/1.42  # SZS output start CNFRefutation
% 1.22/1.42  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.22/1.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.22/1.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.22/1.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.22/1.42  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.22/1.42  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.22/1.42  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 1.22/1.42  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.22/1.42  fof(t5_setfam_1, axiom, ![X1]:(r2_hidden(k1_xboole_0,X1)=>k1_setfam_1(X1)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_setfam_1)).
% 1.22/1.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.22/1.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.22/1.42  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 1.22/1.42  fof(t8_setfam_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 1.22/1.42  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 1.22/1.42  fof(c_0_14, plain, ![X46, X47, X48]:(((r2_hidden(X46,X47)|~r2_hidden(X46,k4_xboole_0(X47,k1_tarski(X48))))&(X46!=X48|~r2_hidden(X46,k4_xboole_0(X47,k1_tarski(X48)))))&(~r2_hidden(X46,X47)|X46=X48|r2_hidden(X46,k4_xboole_0(X47,k1_tarski(X48))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 1.22/1.42  fof(c_0_15, plain, ![X25]:k2_tarski(X25,X25)=k1_tarski(X25), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.22/1.42  fof(c_0_16, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.22/1.42  fof(c_0_17, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.22/1.42  fof(c_0_18, plain, ![X14, X15, X16, X17, X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X18,X17)|(X18=X14|X18=X15|X18=X16)|X17!=k1_enumset1(X14,X15,X16))&(((X19!=X14|r2_hidden(X19,X17)|X17!=k1_enumset1(X14,X15,X16))&(X19!=X15|r2_hidden(X19,X17)|X17!=k1_enumset1(X14,X15,X16)))&(X19!=X16|r2_hidden(X19,X17)|X17!=k1_enumset1(X14,X15,X16))))&((((esk2_4(X20,X21,X22,X23)!=X20|~r2_hidden(esk2_4(X20,X21,X22,X23),X23)|X23=k1_enumset1(X20,X21,X22))&(esk2_4(X20,X21,X22,X23)!=X21|~r2_hidden(esk2_4(X20,X21,X22,X23),X23)|X23=k1_enumset1(X20,X21,X22)))&(esk2_4(X20,X21,X22,X23)!=X22|~r2_hidden(esk2_4(X20,X21,X22,X23),X23)|X23=k1_enumset1(X20,X21,X22)))&(r2_hidden(esk2_4(X20,X21,X22,X23),X23)|(esk2_4(X20,X21,X22,X23)=X20|esk2_4(X20,X21,X22,X23)=X21|esk2_4(X20,X21,X22,X23)=X22)|X23=k1_enumset1(X20,X21,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 1.22/1.42  cnf(c_0_19, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.22/1.42  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.22/1.42  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.22/1.42  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.22/1.42  fof(c_0_23, plain, ![X44, X45]:((k4_xboole_0(k1_tarski(X44),k1_tarski(X45))!=k1_tarski(X44)|X44!=X45)&(X44=X45|k4_xboole_0(k1_tarski(X44),k1_tarski(X45))=k1_tarski(X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 1.22/1.42  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.22/1.42  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.22/1.42  cnf(c_0_26, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])).
% 1.22/1.42  cnf(c_0_27, plain, (X1=X2|k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.22/1.42  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_24, c_0_22])).
% 1.22/1.42  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_25, c_0_22])).
% 1.22/1.42  cnf(c_0_30, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))), inference(er,[status(thm)],[c_0_26])).
% 1.22/1.42  cnf(c_0_31, plain, (X1=X2|k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_20]), c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_22])).
% 1.22/1.42  fof(c_0_32, plain, ![X31, X32, X33, X35, X36, X37, X38, X40]:((((r2_hidden(X33,esk3_3(X31,X32,X33))|~r2_hidden(X33,X32)|X32!=k3_tarski(X31))&(r2_hidden(esk3_3(X31,X32,X33),X31)|~r2_hidden(X33,X32)|X32!=k3_tarski(X31)))&(~r2_hidden(X35,X36)|~r2_hidden(X36,X31)|r2_hidden(X35,X32)|X32!=k3_tarski(X31)))&((~r2_hidden(esk4_2(X37,X38),X38)|(~r2_hidden(esk4_2(X37,X38),X40)|~r2_hidden(X40,X37))|X38=k3_tarski(X37))&((r2_hidden(esk4_2(X37,X38),esk5_2(X37,X38))|r2_hidden(esk4_2(X37,X38),X38)|X38=k3_tarski(X37))&(r2_hidden(esk5_2(X37,X38),X37)|r2_hidden(esk4_2(X37,X38),X38)|X38=k3_tarski(X37))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 1.22/1.42  fof(c_0_33, plain, ![X51, X52]:(~r2_hidden(X51,X52)|r1_tarski(k1_setfam_1(X52),X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 1.22/1.42  cnf(c_0_34, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_28])).
% 1.22/1.42  fof(c_0_35, plain, ![X53]:(~r2_hidden(k1_xboole_0,X53)|k1_setfam_1(X53)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_setfam_1])])).
% 1.22/1.42  cnf(c_0_36, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X1,X1,X3,X4)), inference(er,[status(thm)],[c_0_29])).
% 1.22/1.42  cnf(c_0_37, plain, (X1=X2|~r2_hidden(X2,k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.22/1.42  cnf(c_0_38, plain, (r2_hidden(esk3_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.22/1.42  cnf(c_0_39, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.22/1.42  cnf(c_0_40, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[c_0_34])).
% 1.22/1.42  cnf(c_0_41, plain, (k1_setfam_1(X1)=k1_xboole_0|~r2_hidden(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.22/1.42  cnf(c_0_42, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[c_0_36])).
% 1.22/1.42  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.22/1.42  fof(c_0_44, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.22/1.42  cnf(c_0_45, plain, (r2_hidden(X1,esk3_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.22/1.42  cnf(c_0_46, plain, (esk3_3(k2_enumset1(X1,X1,X1,X1),X2,X3)=X1|X2!=k3_tarski(k2_enumset1(X1,X1,X1,X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.22/1.42  fof(c_0_47, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.22/1.42  cnf(c_0_48, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X3)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.22/1.42  cnf(c_0_49, plain, (k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.22/1.42  cnf(c_0_50, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_20]), c_0_21]), c_0_22])).
% 1.22/1.42  cnf(c_0_51, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.22/1.42  cnf(c_0_52, plain, (r2_hidden(X1,X2)|X3!=k3_tarski(k2_enumset1(X2,X2,X2,X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.22/1.42  cnf(c_0_53, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.22/1.42  cnf(c_0_54, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.22/1.42  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.22/1.42  cnf(c_0_56, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3),X1)|r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.22/1.42  cnf(c_0_57, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_tarski(k2_enumset1(X2,X2,X2,X2)))), inference(er,[status(thm)],[c_0_52])).
% 1.22/1.42  cnf(c_0_58, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 1.22/1.42  cnf(c_0_59, plain, (r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.22/1.42  cnf(c_0_60, plain, (r2_hidden(esk1_2(k3_tarski(k2_enumset1(X1,X1,X1,X1)),X2),X1)|r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X1)),X2)), inference(spm,[status(thm)],[c_0_57, c_0_51])).
% 1.22/1.42  cnf(c_0_61, plain, (k4_xboole_0(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 1.22/1.42  cnf(c_0_62, plain, (r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X1)),X1)), inference(spm,[status(thm)],[c_0_55, c_0_60])).
% 1.22/1.42  fof(c_0_63, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 1.22/1.42  fof(c_0_64, plain, ![X57, X58, X59]:(~r2_hidden(X57,X58)|~r1_tarski(X57,X59)|r1_tarski(k1_setfam_1(X58),X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).
% 1.22/1.42  cnf(c_0_65, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_61])).
% 1.22/1.42  cnf(c_0_66, plain, (r2_hidden(esk3_3(k3_tarski(k2_enumset1(X1,X1,X1,X1)),X2,X3),X1)|X2!=k3_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X1)))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_57, c_0_38])).
% 1.22/1.42  cnf(c_0_67, plain, (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_62])).
% 1.22/1.42  fof(c_0_68, negated_conjecture, k1_setfam_1(k1_tarski(esk7_0))!=esk7_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_63])])])).
% 1.22/1.42  cnf(c_0_69, plain, (r1_tarski(k1_setfam_1(X2),X3)|~r2_hidden(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 1.22/1.42  cnf(c_0_70, plain, (X1!=k3_tarski(k1_xboole_0)|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 1.22/1.42  cnf(c_0_71, negated_conjecture, (k1_setfam_1(k1_tarski(esk7_0))!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_68])).
% 1.22/1.42  cnf(c_0_72, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X2,X3)),X4)|~r1_tarski(X3,X4)), inference(spm,[status(thm)],[c_0_69, c_0_40])).
% 1.22/1.42  cnf(c_0_73, plain, (r1_tarski(X1,X2)|X1!=k3_tarski(k1_xboole_0)), inference(spm,[status(thm)],[c_0_70, c_0_51])).
% 1.22/1.42  cnf(c_0_74, negated_conjecture, (k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))!=esk7_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_20]), c_0_21]), c_0_22])).
% 1.22/1.42  cnf(c_0_75, plain, (k1_setfam_1(k2_enumset1(X1,X1,X2,X3))=k1_xboole_0|~r1_tarski(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_72])).
% 1.22/1.42  fof(c_0_76, plain, ![X54, X55]:((r2_hidden(esk6_2(X54,X55),X54)|(X54=k1_xboole_0|r1_tarski(X55,k1_setfam_1(X54))))&(~r1_tarski(X55,esk6_2(X54,X55))|(X54=k1_xboole_0|r1_tarski(X55,k1_setfam_1(X54))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 1.22/1.42  cnf(c_0_77, plain, (X1=k1_xboole_0|X1!=k3_tarski(k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_73])).
% 1.22/1.42  cnf(c_0_78, negated_conjecture, (~r1_tarski(esk7_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_58])).
% 1.22/1.42  cnf(c_0_79, plain, (r2_hidden(esk6_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 1.22/1.42  cnf(c_0_80, plain, (k2_enumset1(X1,X1,X2,X3)!=k3_tarski(k1_xboole_0)), inference(spm,[status(thm)],[c_0_70, c_0_40])).
% 1.22/1.42  cnf(c_0_81, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_77])).
% 1.22/1.42  cnf(c_0_82, negated_conjecture, (esk7_0!=k3_tarski(k1_xboole_0)), inference(spm,[status(thm)],[c_0_78, c_0_73])).
% 1.22/1.42  cnf(c_0_83, plain, (k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))=k1_xboole_0|r2_hidden(esk6_2(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3),X1)|r1_tarski(X3,k1_setfam_1(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))), inference(spm,[status(thm)],[c_0_50, c_0_79])).
% 1.22/1.42  cnf(c_0_84, plain, (k2_enumset1(X1,X1,X2,X3)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_80, c_0_81])).
% 1.22/1.42  cnf(c_0_85, negated_conjecture, (esk7_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_82, c_0_81])).
% 1.22/1.42  cnf(c_0_86, plain, (X1=X2|r2_hidden(esk6_2(k2_enumset1(X1,X1,X1,X1),X3),k2_enumset1(X1,X1,X1,X1))|r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_31]), c_0_84])).
% 1.22/1.42  cnf(c_0_87, negated_conjecture, (r2_hidden(esk6_2(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),X1),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))|r1_tarski(X1,k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)))|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 1.22/1.42  cnf(c_0_88, negated_conjecture, (r2_hidden(esk6_2(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),X1),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))|r1_tarski(X1,k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)))), inference(er,[status(thm)],[c_0_87])).
% 1.22/1.42  cnf(c_0_89, plain, (r2_hidden(esk5_2(X1,X2),X1)|r2_hidden(esk4_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.22/1.42  cnf(c_0_90, negated_conjecture, (r1_tarski(k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)),esk6_2(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),X1))|r1_tarski(X1,k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)))), inference(spm,[status(thm)],[c_0_39, c_0_88])).
% 1.22/1.42  cnf(c_0_91, plain, (X1=k1_xboole_0|r2_hidden(esk4_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_89]), c_0_81])).
% 1.22/1.42  cnf(c_0_92, negated_conjecture, (esk6_2(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),X1)=k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))|r1_tarski(X1,k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)))|~r1_tarski(esk6_2(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),X1),k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)))), inference(spm,[status(thm)],[c_0_53, c_0_90])).
% 1.22/1.42  cnf(c_0_93, plain, (esk6_2(k2_enumset1(X1,X1,X1,X1),X2)=X1|r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_79]), c_0_84])).
% 1.22/1.42  cnf(c_0_94, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk6_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 1.22/1.42  cnf(c_0_95, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.22/1.42  cnf(c_0_96, plain, (X1=k1_xboole_0|r1_tarski(k1_setfam_1(X1),esk4_2(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_39, c_0_91])).
% 1.22/1.42  cnf(c_0_97, negated_conjecture, (r1_tarski(X1,k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)))|~r1_tarski(esk7_0,k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_74])).
% 1.22/1.42  cnf(c_0_98, plain, (r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X2)))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_93]), c_0_84])).
% 1.22/1.42  cnf(c_0_99, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_95])).
% 1.22/1.42  cnf(c_0_100, plain, (esk4_2(k1_xboole_0,X1)=k1_setfam_1(X1)|X1=k1_xboole_0|~r1_tarski(esk4_2(k1_xboole_0,X1),k1_setfam_1(X1))), inference(spm,[status(thm)],[c_0_53, c_0_96])).
% 1.22/1.42  cnf(c_0_101, negated_conjecture, (r1_tarski(X1,k1_setfam_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])])).
% 1.22/1.42  cnf(c_0_102, plain, (esk4_2(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_91]), c_0_84])).
% 1.22/1.42  cnf(c_0_103, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102]), c_0_74]), c_0_84]), ['proof']).
% 1.22/1.42  # SZS output end CNFRefutation
% 1.22/1.42  # Proof object total steps             : 104
% 1.22/1.42  # Proof object clause steps            : 75
% 1.22/1.42  # Proof object formula steps           : 29
% 1.22/1.42  # Proof object conjectures             : 15
% 1.22/1.42  # Proof object clause conjectures      : 12
% 1.22/1.42  # Proof object formula conjectures     : 3
% 1.22/1.42  # Proof object initial clauses used    : 21
% 1.22/1.42  # Proof object initial formulas used   : 14
% 1.22/1.42  # Proof object generating inferences   : 42
% 1.22/1.42  # Proof object simplifying inferences  : 39
% 1.22/1.42  # Training examples: 0 positive, 0 negative
% 1.22/1.42  # Parsed axioms                        : 16
% 1.22/1.42  # Removed by relevancy pruning/SinE    : 0
% 1.22/1.42  # Initial clauses                      : 37
% 1.22/1.42  # Removed in clause preprocessing      : 3
% 1.22/1.42  # Initial clauses in saturation        : 34
% 1.22/1.42  # Processed clauses                    : 11172
% 1.22/1.42  # ...of these trivial                  : 218
% 1.22/1.42  # ...subsumed                          : 9623
% 1.22/1.42  # ...remaining for further processing  : 1331
% 1.22/1.42  # Other redundant clauses eliminated   : 773
% 1.22/1.42  # Clauses deleted for lack of memory   : 0
% 1.22/1.42  # Backward-subsumed                    : 63
% 1.22/1.42  # Backward-rewritten                   : 10
% 1.22/1.42  # Generated clauses                    : 96355
% 1.22/1.42  # ...of the previous two non-trivial   : 86610
% 1.22/1.42  # Contextual simplify-reflections      : 16
% 1.22/1.42  # Paramodulations                      : 95181
% 1.22/1.42  # Factorizations                       : 114
% 1.22/1.42  # Equation resolutions                 : 1060
% 1.22/1.42  # Propositional unsat checks           : 0
% 1.22/1.42  #    Propositional check models        : 0
% 1.22/1.42  #    Propositional check unsatisfiable : 0
% 1.22/1.42  #    Propositional clauses             : 0
% 1.22/1.42  #    Propositional clauses after purity: 0
% 1.22/1.42  #    Propositional unsat core size     : 0
% 1.22/1.42  #    Propositional preprocessing time  : 0.000
% 1.22/1.42  #    Propositional encoding time       : 0.000
% 1.22/1.42  #    Propositional solver time         : 0.000
% 1.22/1.42  #    Success case prop preproc time    : 0.000
% 1.22/1.42  #    Success case prop encoding time   : 0.000
% 1.22/1.42  #    Success case prop solver time     : 0.000
% 1.22/1.42  # Current number of processed clauses  : 1218
% 1.22/1.42  #    Positive orientable unit clauses  : 21
% 1.22/1.42  #    Positive unorientable unit clauses: 0
% 1.22/1.42  #    Negative unit clauses             : 9
% 1.22/1.42  #    Non-unit-clauses                  : 1188
% 1.22/1.42  # Current number of unprocessed clauses: 75329
% 1.22/1.42  # ...number of literals in the above   : 382930
% 1.22/1.42  # Current number of archived formulas  : 0
% 1.22/1.42  # Current number of archived clauses   : 109
% 1.22/1.42  # Clause-clause subsumption calls (NU) : 164774
% 1.22/1.42  # Rec. Clause-clause subsumption calls : 73677
% 1.22/1.42  # Non-unit clause-clause subsumptions  : 7333
% 1.22/1.42  # Unit Clause-clause subsumption calls : 345
% 1.22/1.42  # Rewrite failures with RHS unbound    : 0
% 1.22/1.42  # BW rewrite match attempts            : 45
% 1.22/1.42  # BW rewrite match successes           : 4
% 1.22/1.42  # Condensation attempts                : 0
% 1.22/1.42  # Condensation successes               : 0
% 1.22/1.42  # Termbank termtop insertions          : 1700454
% 1.22/1.42  
% 1.22/1.42  # -------------------------------------------------
% 1.22/1.42  # User time                : 1.055 s
% 1.22/1.42  # System time              : 0.042 s
% 1.22/1.42  # Total time               : 1.097 s
% 1.22/1.42  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
