%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 417 expanded)
%              Number of clauses        :   62 ( 188 expanded)
%              Number of leaves         :   14 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          :  184 ( 787 expanded)
%              Number of equality atoms :   95 ( 502 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(t148_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & k3_xboole_0(X2,X3) = k1_tarski(X4)
        & r2_hidden(X4,X1) )
     => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(l35_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t50_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_14,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43,X44] :
      ( ( ~ r2_hidden(X40,X39)
        | X40 = X37
        | X40 = X38
        | X39 != k2_tarski(X37,X38) )
      & ( X41 != X37
        | r2_hidden(X41,X39)
        | X39 != k2_tarski(X37,X38) )
      & ( X41 != X38
        | r2_hidden(X41,X39)
        | X39 != k2_tarski(X37,X38) )
      & ( esk3_3(X42,X43,X44) != X42
        | ~ r2_hidden(esk3_3(X42,X43,X44),X44)
        | X44 = k2_tarski(X42,X43) )
      & ( esk3_3(X42,X43,X44) != X43
        | ~ r2_hidden(esk3_3(X42,X43,X44),X44)
        | X44 = k2_tarski(X42,X43) )
      & ( r2_hidden(esk3_3(X42,X43,X44),X44)
        | esk3_3(X42,X43,X44) = X42
        | esk3_3(X42,X43,X44) = X43
        | X44 = k2_tarski(X42,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X47,X48] : k2_enumset1(X47,X47,X47,X48) = k2_tarski(X47,X48) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0)
    & k3_xboole_0(esk5_0,esk6_0) = k1_tarski(esk7_0)
    & r2_hidden(esk7_0,esk4_0)
    & k3_xboole_0(esk4_0,esk6_0) != k1_tarski(esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X46] : k2_tarski(X46,X46) = k1_tarski(X46) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X29,X30] : k4_xboole_0(X29,k4_xboole_0(X29,X30)) = k3_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_22,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k4_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk6_0) = k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)) = k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_18]),c_0_26])).

fof(c_0_31,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k3_xboole_0(X27,X28)) = k4_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk7_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_40,plain,(
    ! [X49,X50] :
      ( ( k4_xboole_0(k1_tarski(X49),X50) != k1_xboole_0
        | r2_hidden(X49,X50) )
      & ( ~ r2_hidden(X49,X50)
        | k4_xboole_0(k1_tarski(X49),X50) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).

fof(c_0_41,plain,(
    ! [X31,X32,X33] : k3_xboole_0(X31,k4_xboole_0(X32,X33)) = k4_xboole_0(k3_xboole_0(X31,X32),X33) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k4_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_26])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k4_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk7_0,k4_xboole_0(esk5_0,X1))
    | r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_25]),c_0_18])).

fof(c_0_51,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | k3_xboole_0(X25,X26) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_52,plain,(
    ! [X34,X35,X36] : k3_xboole_0(X34,k4_xboole_0(X35,X36)) = k4_xboole_0(k3_xboole_0(X34,X35),k3_xboole_0(X34,X36)) ),
    inference(variable_rename,[status(thm)],[t50_xboole_1])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k4_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_39])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_26]),c_0_26])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_56,plain,(
    ! [X22] : k3_xboole_0(X22,X22) = X22 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_29])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_29])).

cnf(c_0_59,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_60,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk7_0,k4_xboole_0(esk6_0,X1))
    | r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_55])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_67,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | r2_hidden(esk2_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_61,c_0_26])).

fof(c_0_69,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk7_0,k4_xboole_0(esk6_0,k4_xboole_0(X1,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_65,c_0_26])).

cnf(c_0_73,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_33])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_76,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_70,c_0_54])).

cnf(c_0_77,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(X1,esk4_0))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_71]),c_0_30]),c_0_54])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk5_0) = k4_xboole_0(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk6_0) != k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_26]),c_0_26])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_76]),c_0_43])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(X1,esk4_0)))) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_77]),c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,X1))) = k4_xboole_0(esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_79]),c_0_72])).

cnf(c_0_85,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)) != k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_25]),c_0_18]),c_0_26])).

cnf(c_0_86,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_81]),c_0_54]),c_0_76])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(esk6_0,k4_xboole_0(esk5_0,k4_xboole_0(X1,esk4_0))) = k4_xboole_0(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,X1)) = k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)) != k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_85,c_0_30])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_81]),c_0_88]),c_0_88]),c_0_43]),c_0_81]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.51  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.20/0.51  # and selection function SelectCQArNTNpEqFirst.
% 0.20/0.51  #
% 0.20/0.51  # Preprocessing time       : 0.028 s
% 0.20/0.51  # Presaturation interreduction done
% 0.20/0.51  
% 0.20/0.51  # Proof found!
% 0.20/0.51  # SZS status Theorem
% 0.20/0.51  # SZS output start CNFRefutation
% 0.20/0.51  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.51  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.20/0.51  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 0.20/0.51  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.51  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.51  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.51  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.51  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.20/0.51  fof(l35_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 0.20/0.51  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.20/0.51  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.51  fof(t50_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 0.20/0.51  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.51  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.51  fof(c_0_14, plain, ![X37, X38, X39, X40, X41, X42, X43, X44]:(((~r2_hidden(X40,X39)|(X40=X37|X40=X38)|X39!=k2_tarski(X37,X38))&((X41!=X37|r2_hidden(X41,X39)|X39!=k2_tarski(X37,X38))&(X41!=X38|r2_hidden(X41,X39)|X39!=k2_tarski(X37,X38))))&(((esk3_3(X42,X43,X44)!=X42|~r2_hidden(esk3_3(X42,X43,X44),X44)|X44=k2_tarski(X42,X43))&(esk3_3(X42,X43,X44)!=X43|~r2_hidden(esk3_3(X42,X43,X44),X44)|X44=k2_tarski(X42,X43)))&(r2_hidden(esk3_3(X42,X43,X44),X44)|(esk3_3(X42,X43,X44)=X42|esk3_3(X42,X43,X44)=X43)|X44=k2_tarski(X42,X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.51  fof(c_0_15, plain, ![X47, X48]:k2_enumset1(X47,X47,X47,X48)=k2_tarski(X47,X48), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.20/0.51  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 0.20/0.51  cnf(c_0_17, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.51  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.51  fof(c_0_19, negated_conjecture, (((r1_tarski(esk4_0,esk5_0)&k3_xboole_0(esk5_0,esk6_0)=k1_tarski(esk7_0))&r2_hidden(esk7_0,esk4_0))&k3_xboole_0(esk4_0,esk6_0)!=k1_tarski(esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.51  fof(c_0_20, plain, ![X46]:k2_tarski(X46,X46)=k1_tarski(X46), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.51  fof(c_0_21, plain, ![X29, X30]:k4_xboole_0(X29,k4_xboole_0(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.51  fof(c_0_22, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k4_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k4_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.51  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.51  cnf(c_0_24, negated_conjecture, (k3_xboole_0(esk5_0,esk6_0)=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.51  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.51  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.51  fof(c_0_27, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.51  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_29, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).
% 0.20/0.51  cnf(c_0_30, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))=k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_18]), c_0_26])).
% 0.20/0.51  fof(c_0_31, plain, ![X27, X28]:k4_xboole_0(X27,k3_xboole_0(X27,X28))=k4_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.20/0.51  cnf(c_0_32, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.51  cnf(c_0_33, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.51  cnf(c_0_34, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.51  cnf(c_0_35, negated_conjecture, (r2_hidden(esk7_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.51  cnf(c_0_36, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.51  cnf(c_0_37, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_38, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.51  cnf(c_0_39, negated_conjecture, (r2_hidden(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.51  fof(c_0_40, plain, ![X49, X50]:((k4_xboole_0(k1_tarski(X49),X50)!=k1_xboole_0|r2_hidden(X49,X50))&(~r2_hidden(X49,X50)|k4_xboole_0(k1_tarski(X49),X50)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).
% 0.20/0.51  fof(c_0_41, plain, ![X31, X32, X33]:k3_xboole_0(X31,k4_xboole_0(X32,X33))=k4_xboole_0(k3_xboole_0(X31,X32),X33), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.20/0.51  cnf(c_0_42, negated_conjecture, (~r2_hidden(esk7_0,k4_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.51  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_26])).
% 0.20/0.51  cnf(c_0_44, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_37])).
% 0.20/0.51  cnf(c_0_45, negated_conjecture, (r2_hidden(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.51  cnf(c_0_46, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.51  cnf(c_0_47, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.51  cnf(c_0_48, negated_conjecture, (~r2_hidden(esk7_0,k4_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.51  cnf(c_0_49, negated_conjecture, (r2_hidden(esk7_0,k4_xboole_0(esk5_0,X1))|r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.51  cnf(c_0_50, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_25]), c_0_18])).
% 0.20/0.51  fof(c_0_51, plain, ![X25, X26]:(~r1_tarski(X25,X26)|k3_xboole_0(X25,X26)=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.51  fof(c_0_52, plain, ![X34, X35, X36]:k3_xboole_0(X34,k4_xboole_0(X35,X36))=k4_xboole_0(k3_xboole_0(X34,X35),k3_xboole_0(X34,X36)), inference(variable_rename,[status(thm)],[t50_xboole_1])).
% 0.20/0.51  cnf(c_0_53, negated_conjecture, (~r2_hidden(esk7_0,k4_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_39])).
% 0.20/0.51  cnf(c_0_54, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_26]), c_0_26])).
% 0.20/0.51  cnf(c_0_55, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.51  fof(c_0_56, plain, ![X22]:k3_xboole_0(X22,X22)=X22, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.51  cnf(c_0_57, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X1)))), inference(spm,[status(thm)],[c_0_34, c_0_29])).
% 0.20/0.51  cnf(c_0_58, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_29])).
% 0.20/0.51  cnf(c_0_59, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_60, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_61, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.51  cnf(c_0_62, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.51  cnf(c_0_63, negated_conjecture, (~r2_hidden(esk7_0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,esk4_0))))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.51  cnf(c_0_64, negated_conjecture, (r2_hidden(esk7_0,k4_xboole_0(esk6_0,X1))|r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_55])).
% 0.20/0.51  cnf(c_0_65, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.51  cnf(c_0_66, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.51  cnf(c_0_67, plain, (X1=k4_xboole_0(X2,X2)|r2_hidden(esk2_3(X2,X2,X1),X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.51  cnf(c_0_68, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_61, c_0_26])).
% 0.20/0.51  fof(c_0_69, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.51  cnf(c_0_70, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_26]), c_0_26]), c_0_26])).
% 0.20/0.51  cnf(c_0_71, negated_conjecture, (r2_hidden(esk7_0,k4_xboole_0(esk6_0,k4_xboole_0(X1,esk4_0)))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.51  cnf(c_0_72, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_65, c_0_26])).
% 0.20/0.51  cnf(c_0_73, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.51  cnf(c_0_74, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))=esk4_0), inference(spm,[status(thm)],[c_0_68, c_0_33])).
% 0.20/0.51  cnf(c_0_75, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.51  cnf(c_0_76, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3)))))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_70, c_0_54])).
% 0.20/0.51  cnf(c_0_77, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(X1,esk4_0)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_71]), c_0_30]), c_0_54])).
% 0.20/0.51  cnf(c_0_78, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.51  cnf(c_0_79, negated_conjecture, (k4_xboole_0(esk4_0,esk5_0)=k4_xboole_0(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_74])).
% 0.20/0.51  cnf(c_0_80, negated_conjecture, (k3_xboole_0(esk4_0,esk6_0)!=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.51  cnf(c_0_81, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_26]), c_0_26])).
% 0.20/0.51  cnf(c_0_82, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_76]), c_0_43])).
% 0.20/0.51  cnf(c_0_83, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,k4_xboole_0(X1,esk4_0))))=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_77]), c_0_78])).
% 0.20/0.51  cnf(c_0_84, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,X1)))=k4_xboole_0(esk4_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_79]), c_0_72])).
% 0.20/0.51  cnf(c_0_85, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))!=k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_25]), c_0_18]), c_0_26])).
% 0.20/0.51  cnf(c_0_86, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))=k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_81]), c_0_54]), c_0_76])).
% 0.20/0.51  cnf(c_0_87, negated_conjecture, (k4_xboole_0(esk6_0,k4_xboole_0(esk5_0,k4_xboole_0(X1,esk4_0)))=k4_xboole_0(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.51  cnf(c_0_88, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,X1))=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_43, c_0_84])).
% 0.20/0.51  cnf(c_0_89, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))!=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))), inference(rw,[status(thm)],[c_0_85, c_0_30])).
% 0.20/0.51  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_81]), c_0_88]), c_0_88]), c_0_43]), c_0_81]), c_0_89]), ['proof']).
% 0.20/0.51  # SZS output end CNFRefutation
% 0.20/0.51  # Proof object total steps             : 91
% 0.20/0.51  # Proof object clause steps            : 62
% 0.20/0.51  # Proof object formula steps           : 29
% 0.20/0.51  # Proof object conjectures             : 29
% 0.20/0.51  # Proof object clause conjectures      : 26
% 0.20/0.51  # Proof object formula conjectures     : 3
% 0.20/0.51  # Proof object initial clauses used    : 20
% 0.20/0.51  # Proof object initial formulas used   : 14
% 0.20/0.51  # Proof object generating inferences   : 26
% 0.20/0.51  # Proof object simplifying inferences  : 39
% 0.20/0.51  # Training examples: 0 positive, 0 negative
% 0.20/0.51  # Parsed axioms                        : 15
% 0.20/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.51  # Initial clauses                      : 33
% 0.20/0.51  # Removed in clause preprocessing      : 3
% 0.20/0.51  # Initial clauses in saturation        : 30
% 0.20/0.51  # Processed clauses                    : 2290
% 0.20/0.51  # ...of these trivial                  : 55
% 0.20/0.51  # ...subsumed                          : 1782
% 0.20/0.51  # ...remaining for further processing  : 453
% 0.20/0.51  # Other redundant clauses eliminated   : 38
% 0.20/0.51  # Clauses deleted for lack of memory   : 0
% 0.20/0.51  # Backward-subsumed                    : 0
% 0.20/0.51  # Backward-rewritten                   : 179
% 0.20/0.51  # Generated clauses                    : 11687
% 0.20/0.51  # ...of the previous two non-trivial   : 9156
% 0.20/0.51  # Contextual simplify-reflections      : 0
% 0.20/0.51  # Paramodulations                      : 11617
% 0.20/0.51  # Factorizations                       : 34
% 0.20/0.51  # Equation resolutions                 : 38
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
% 0.20/0.51  # Current number of processed clauses  : 237
% 0.20/0.51  #    Positive orientable unit clauses  : 68
% 0.20/0.51  #    Positive unorientable unit clauses: 3
% 0.20/0.51  #    Negative unit clauses             : 58
% 0.20/0.51  #    Non-unit-clauses                  : 108
% 0.20/0.51  # Current number of unprocessed clauses: 6448
% 0.20/0.51  # ...number of literals in the above   : 12567
% 0.20/0.51  # Current number of archived formulas  : 0
% 0.20/0.51  # Current number of archived clauses   : 211
% 0.20/0.51  # Clause-clause subsumption calls (NU) : 1686
% 0.20/0.51  # Rec. Clause-clause subsumption calls : 1365
% 0.20/0.51  # Non-unit clause-clause subsumptions  : 127
% 0.20/0.51  # Unit Clause-clause subsumption calls : 2647
% 0.20/0.51  # Rewrite failures with RHS unbound    : 0
% 0.20/0.51  # BW rewrite match attempts            : 1582
% 0.20/0.51  # BW rewrite match successes           : 203
% 0.20/0.51  # Condensation attempts                : 0
% 0.20/0.51  # Condensation successes               : 0
% 0.20/0.51  # Termbank termtop insertions          : 164452
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.167 s
% 0.20/0.51  # System time              : 0.009 s
% 0.20/0.51  # Total time               : 0.176 s
% 0.20/0.51  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
