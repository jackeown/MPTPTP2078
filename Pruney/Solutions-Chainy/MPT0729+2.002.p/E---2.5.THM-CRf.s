%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:04 EST 2020

% Result     : Theorem 1.19s
% Output     : CNFRefutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  143 (3254 expanded)
%              Number of clauses        :   98 (1347 expanded)
%              Number of leaves         :   22 ( 946 expanded)
%              Depth                    :   21
%              Number of atoms          :  257 (3980 expanded)
%              Number of equality atoms :   95 (3216 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t12_ordinal1,conjecture,(
    ! [X1,X2] :
      ( k1_ordinal1(X1) = k1_ordinal1(X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(c_0_22,plain,(
    ! [X43,X44] : k3_tarski(k2_tarski(X43,X44)) = k2_xboole_0(X43,X44) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X34,X35] : k1_enumset1(X34,X34,X35) = k2_tarski(X34,X35) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k1_ordinal1(X1) = k1_ordinal1(X2)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t12_ordinal1])).

fof(c_0_25,plain,(
    ! [X53] : k1_ordinal1(X53) = k2_xboole_0(X53,k1_tarski(X53)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_26,plain,(
    ! [X33] : k2_tarski(X33,X33) = k1_tarski(X33) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_27,plain,(
    ! [X29,X30] : r1_tarski(X29,k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_28,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X36,X37,X38] : k2_enumset1(X36,X36,X37,X38) = k1_enumset1(X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_31,plain,(
    ! [X39,X40,X41,X42] : k3_enumset1(X39,X39,X40,X41,X42) = k2_enumset1(X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_32,negated_conjecture,
    ( k1_ordinal1(esk2_0) = k1_ordinal1(esk3_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_33,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X20] : k2_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_36,plain,(
    ! [X31,X32] : k2_tarski(X31,X32) = k2_tarski(X32,X31) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( k1_ordinal1(esk2_0) = k1_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_43,plain,(
    ! [X23,X24,X25] : k4_xboole_0(k4_xboole_0(X23,X24),X25) = k4_xboole_0(X23,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_46,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_tarski(X26,k2_xboole_0(X27,X28))
      | r1_tarski(k4_xboole_0(X26,X27),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_47,plain,(
    ! [X18,X19] :
      ( ( k4_xboole_0(X18,X19) != k1_xboole_0
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | k4_xboole_0(X18,X19) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) = k3_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_42]),c_0_29]),c_0_29]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_51,plain,(
    ! [X51,X52] :
      ( ( k4_xboole_0(X51,k1_tarski(X52)) != X51
        | ~ r2_hidden(X52,X51) )
      & ( r2_hidden(X52,X51)
        | k4_xboole_0(X51,k1_tarski(X52)) = X51 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_52,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_53,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_54,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_29]),c_0_29]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

cnf(c_0_55,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_62,plain,(
    ! [X21,X22] : k2_xboole_0(X21,k4_xboole_0(X22,X21)) = k2_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_63,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) = k4_xboole_0(k4_xboole_0(X1,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_49]),c_0_58])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_34]),c_0_29]),c_0_39]),c_0_40])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_61])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_71,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_72,plain,(
    ! [X45,X46,X47] :
      ( ( r2_hidden(X45,X47)
        | ~ r1_tarski(k2_tarski(X45,X46),X47) )
      & ( r2_hidden(X46,X47)
        | ~ r1_tarski(k2_tarski(X45,X46),X47) )
      & ( ~ r2_hidden(X45,X47)
        | ~ r2_hidden(X46,X47)
        | r1_tarski(k2_tarski(X45,X46),X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_73,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_54])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_49])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_65,c_0_58])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k4_xboole_0(X1,esk2_0)
    | r2_hidden(esk2_0,k4_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_68])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_69])).

cnf(c_0_79,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k4_xboole_0(X2,X1))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

cnf(c_0_80,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = k1_xboole_0
    | r2_hidden(esk3_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_67])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) = k1_xboole_0
    | r2_hidden(esk2_0,k4_xboole_0(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_85,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_79]),c_0_58])).

cnf(c_0_86,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k3_enumset1(X3,X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_29]),c_0_39]),c_0_40])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)
    | r2_hidden(esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_67])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_90,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)) = esk3_0
    | r2_hidden(esk3_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_83]),c_0_54]),c_0_61])).

cnf(c_0_91,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk2_0)) = esk2_0
    | r2_hidden(esk2_0,k4_xboole_0(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_84]),c_0_54]),c_0_61]),c_0_54])).

cnf(c_0_92,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_93,plain,(
    ! [X55,X56] :
      ( ~ r2_hidden(X55,X56)
      | ~ r1_tarski(X56,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_95,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_85])).

cnf(c_0_96,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k3_enumset1(X1,X1,X1,X1,X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_67])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))
    | r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_98,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk2_0,k4_xboole_0(esk3_0,esk2_0))
    | r2_hidden(esk3_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92])).

cnf(c_0_100,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_101,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_102,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r2_hidden(esk2_0,X1)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(esk2_0,esk3_0))
    | r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_105,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_106,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_29]),c_0_39]),c_0_40])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,X1),esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_107])).

fof(c_0_110,plain,(
    ! [X48,X49,X50] :
      ( ( r2_hidden(X48,X49)
        | ~ r2_hidden(X48,k4_xboole_0(X49,k1_tarski(X50))) )
      & ( X48 != X50
        | ~ r2_hidden(X48,k4_xboole_0(X49,k1_tarski(X50))) )
      & ( ~ r2_hidden(X48,X49)
        | X48 = X50
        | r2_hidden(X48,k4_xboole_0(X49,k1_tarski(X50))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_57])).

fof(c_0_112,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_113,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | k4_xboole_0(k4_xboole_0(X1,X2),X3) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_58])).

cnf(c_0_114,negated_conjecture,
    ( k4_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_109])).

cnf(c_0_115,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    | r2_hidden(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_67])).

cnf(c_0_117,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_78])])).

cnf(c_0_119,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_34]),c_0_29]),c_0_39]),c_0_40])).

cnf(c_0_120,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = k1_xboole_0
    | r2_hidden(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_116])).

cnf(c_0_121,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_107])).

cnf(c_0_122,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_77])).

cnf(c_0_123,plain,
    ( ~ r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X4,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_58])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_118])).

fof(c_0_125,plain,(
    ! [X54] : r2_hidden(X54,k1_ordinal1(X54)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_126,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_119])).

cnf(c_0_127,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk3_0),esk2_0) = k4_xboole_0(X1,esk3_0)
    | r2_hidden(esk3_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_90])).

cnf(c_0_128,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_129,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_77]),c_0_122])).

cnf(c_0_130,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k4_xboole_0(k4_xboole_0(X1,esk3_0),X2)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_131,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_61]),c_0_61])).

cnf(c_0_132,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_133,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_125])).

cnf(c_0_134,negated_conjecture,
    ( r2_hidden(esk2_0,k4_xboole_0(X1,esk2_0))
    | ~ r2_hidden(esk3_0,k4_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_76])).

cnf(c_0_135,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk3_0),esk2_0) = k4_xboole_0(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_128]),c_0_129])).

cnf(c_0_136,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k4_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_137,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_132])).

cnf(c_0_138,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_42]),c_0_29]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

cnf(c_0_139,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k4_xboole_0(X1,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_136])).

cnf(c_0_140,plain,
    ( r2_hidden(X1,k4_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1))),X2))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_141,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_100,c_0_68])).

cnf(c_0_142,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_141]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.19/1.36  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 1.19/1.36  # and selection function SelectNegativeLiterals.
% 1.19/1.36  #
% 1.19/1.36  # Preprocessing time       : 0.028 s
% 1.19/1.36  # Presaturation interreduction done
% 1.19/1.36  
% 1.19/1.36  # Proof found!
% 1.19/1.36  # SZS status Theorem
% 1.19/1.36  # SZS output start CNFRefutation
% 1.19/1.36  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.19/1.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.19/1.36  fof(t12_ordinal1, conjecture, ![X1, X2]:(k1_ordinal1(X1)=k1_ordinal1(X2)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_ordinal1)).
% 1.19/1.36  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.19/1.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.19/1.36  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.19/1.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.19/1.36  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.19/1.36  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.19/1.36  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.19/1.36  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.19/1.36  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.19/1.36  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.19/1.36  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.19/1.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.19/1.36  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.19/1.36  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.19/1.36  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.19/1.36  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.19/1.36  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.19/1.36  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 1.19/1.36  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.19/1.36  fof(c_0_22, plain, ![X43, X44]:k3_tarski(k2_tarski(X43,X44))=k2_xboole_0(X43,X44), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.19/1.36  fof(c_0_23, plain, ![X34, X35]:k1_enumset1(X34,X34,X35)=k2_tarski(X34,X35), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.19/1.36  fof(c_0_24, negated_conjecture, ~(![X1, X2]:(k1_ordinal1(X1)=k1_ordinal1(X2)=>X1=X2)), inference(assume_negation,[status(cth)],[t12_ordinal1])).
% 1.19/1.36  fof(c_0_25, plain, ![X53]:k1_ordinal1(X53)=k2_xboole_0(X53,k1_tarski(X53)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 1.19/1.36  fof(c_0_26, plain, ![X33]:k2_tarski(X33,X33)=k1_tarski(X33), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.19/1.36  fof(c_0_27, plain, ![X29, X30]:r1_tarski(X29,k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 1.19/1.36  cnf(c_0_28, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.19/1.36  cnf(c_0_29, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.19/1.36  fof(c_0_30, plain, ![X36, X37, X38]:k2_enumset1(X36,X36,X37,X38)=k1_enumset1(X36,X37,X38), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.19/1.36  fof(c_0_31, plain, ![X39, X40, X41, X42]:k3_enumset1(X39,X39,X40,X41,X42)=k2_enumset1(X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.19/1.36  fof(c_0_32, negated_conjecture, (k1_ordinal1(esk2_0)=k1_ordinal1(esk3_0)&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 1.19/1.36  cnf(c_0_33, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.19/1.36  cnf(c_0_34, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.19/1.36  fof(c_0_35, plain, ![X20]:k2_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t1_boole])).
% 1.19/1.36  fof(c_0_36, plain, ![X31, X32]:k2_tarski(X31,X32)=k2_tarski(X32,X31), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.19/1.36  cnf(c_0_37, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.19/1.36  cnf(c_0_38, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 1.19/1.36  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.19/1.36  cnf(c_0_40, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.19/1.36  cnf(c_0_41, negated_conjecture, (k1_ordinal1(esk2_0)=k1_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.19/1.36  cnf(c_0_42, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 1.19/1.36  fof(c_0_43, plain, ![X23, X24, X25]:k4_xboole_0(k4_xboole_0(X23,X24),X25)=k4_xboole_0(X23,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.19/1.36  cnf(c_0_44, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.19/1.36  cnf(c_0_45, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.19/1.36  fof(c_0_46, plain, ![X26, X27, X28]:(~r1_tarski(X26,k2_xboole_0(X27,X28))|r1_tarski(k4_xboole_0(X26,X27),X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 1.19/1.36  fof(c_0_47, plain, ![X18, X19]:((k4_xboole_0(X18,X19)!=k1_xboole_0|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|k4_xboole_0(X18,X19)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.19/1.36  cnf(c_0_48, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])).
% 1.19/1.36  cnf(c_0_49, negated_conjecture, (k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))=k3_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_42]), c_0_29]), c_0_29]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 1.19/1.36  cnf(c_0_50, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.19/1.36  fof(c_0_51, plain, ![X51, X52]:((k4_xboole_0(X51,k1_tarski(X52))!=X51|~r2_hidden(X52,X51))&(r2_hidden(X52,X51)|k4_xboole_0(X51,k1_tarski(X52))=X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 1.19/1.36  fof(c_0_52, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.19/1.36  cnf(c_0_53, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_38]), c_0_39]), c_0_40])).
% 1.19/1.36  cnf(c_0_54, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_29]), c_0_29]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 1.19/1.36  cnf(c_0_55, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.19/1.36  cnf(c_0_56, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.19/1.36  cnf(c_0_57, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.19/1.36  cnf(c_0_58, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_38]), c_0_39]), c_0_40])).
% 1.19/1.36  cnf(c_0_59, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.19/1.36  cnf(c_0_60, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.19/1.36  cnf(c_0_61, plain, (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 1.19/1.36  fof(c_0_62, plain, ![X21, X22]:k2_xboole_0(X21,k4_xboole_0(X22,X21))=k2_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 1.19/1.36  cnf(c_0_63, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_38]), c_0_39]), c_0_40])).
% 1.19/1.36  cnf(c_0_64, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_48, c_0_54])).
% 1.19/1.36  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 1.19/1.36  cnf(c_0_66, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))=k4_xboole_0(k4_xboole_0(X1,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_49]), c_0_58])).
% 1.19/1.36  cnf(c_0_67, plain, (k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_34]), c_0_29]), c_0_39]), c_0_40])).
% 1.19/1.36  cnf(c_0_68, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_60])).
% 1.19/1.36  cnf(c_0_69, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_48, c_0_61])).
% 1.19/1.36  cnf(c_0_70, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.19/1.36  fof(c_0_71, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 1.19/1.36  fof(c_0_72, plain, ![X45, X46, X47]:(((r2_hidden(X45,X47)|~r1_tarski(k2_tarski(X45,X46),X47))&(r2_hidden(X46,X47)|~r1_tarski(k2_tarski(X45,X46),X47)))&(~r2_hidden(X45,X47)|~r2_hidden(X46,X47)|r1_tarski(k2_tarski(X45,X46),X47))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 1.19/1.36  cnf(c_0_73, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))), inference(spm,[status(thm)],[c_0_63, c_0_54])).
% 1.19/1.36  cnf(c_0_74, negated_conjecture, (r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(spm,[status(thm)],[c_0_64, c_0_49])).
% 1.19/1.36  cnf(c_0_75, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_65, c_0_58])).
% 1.19/1.36  cnf(c_0_76, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k4_xboole_0(X1,esk2_0)|r2_hidden(esk2_0,k4_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 1.19/1.36  cnf(c_0_77, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_68])).
% 1.19/1.36  cnf(c_0_78, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_69])).
% 1.19/1.36  cnf(c_0_79, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k4_xboole_0(X2,X1)))=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 1.19/1.36  cnf(c_0_80, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.19/1.36  cnf(c_0_81, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.19/1.36  cnf(c_0_82, negated_conjecture, (r1_tarski(k4_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),esk3_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 1.19/1.36  cnf(c_0_83, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=k1_xboole_0|r2_hidden(esk3_0,k4_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_75, c_0_67])).
% 1.19/1.36  cnf(c_0_84, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)=k1_xboole_0|r2_hidden(esk2_0,k4_xboole_0(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 1.19/1.36  cnf(c_0_85, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_79]), c_0_58])).
% 1.19/1.36  cnf(c_0_86, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_80])).
% 1.19/1.36  cnf(c_0_87, plain, (r2_hidden(X1,X2)|~r1_tarski(k3_enumset1(X3,X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_29]), c_0_39]), c_0_40])).
% 1.19/1.36  cnf(c_0_88, negated_conjecture, (r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)|r2_hidden(esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_82, c_0_67])).
% 1.19/1.36  cnf(c_0_89, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.19/1.36  cnf(c_0_90, negated_conjecture, (k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))=esk3_0|r2_hidden(esk3_0,k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_83]), c_0_54]), c_0_61])).
% 1.19/1.36  cnf(c_0_91, negated_conjecture, (k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk2_0))=esk2_0|r2_hidden(esk2_0,k4_xboole_0(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_84]), c_0_54]), c_0_61]), c_0_54])).
% 1.19/1.36  cnf(c_0_92, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.19/1.36  fof(c_0_93, plain, ![X55, X56]:(~r2_hidden(X55,X56)|~r1_tarski(X56,X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 1.19/1.36  cnf(c_0_94, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.19/1.36  cnf(c_0_95, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_85])).
% 1.19/1.36  cnf(c_0_96, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k3_enumset1(X1,X1,X1,X1,X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_86, c_0_67])).
% 1.19/1.36  cnf(c_0_97, negated_conjecture, (r2_hidden(esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))|r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 1.19/1.36  cnf(c_0_98, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_89])).
% 1.19/1.36  cnf(c_0_99, negated_conjecture, (r2_hidden(esk2_0,k4_xboole_0(esk3_0,esk2_0))|r2_hidden(esk3_0,k4_xboole_0(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92])).
% 1.19/1.36  cnf(c_0_100, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 1.19/1.36  cnf(c_0_101, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 1.19/1.36  cnf(c_0_102, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.19/1.36  cnf(c_0_103, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r2_hidden(esk2_0,X1)|~r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 1.19/1.36  cnf(c_0_104, negated_conjecture, (r2_hidden(esk3_0,k4_xboole_0(esk2_0,esk3_0))|r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 1.19/1.36  cnf(c_0_105, plain, (~r2_hidden(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 1.19/1.36  cnf(c_0_106, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_29]), c_0_39]), c_0_40])).
% 1.19/1.36  cnf(c_0_107, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_105])).
% 1.19/1.36  cnf(c_0_108, negated_conjecture, (r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,X1),esk3_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 1.19/1.36  cnf(c_0_109, negated_conjecture, (r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_108, c_0_107])).
% 1.19/1.36  fof(c_0_110, plain, ![X48, X49, X50]:(((r2_hidden(X48,X49)|~r2_hidden(X48,k4_xboole_0(X49,k1_tarski(X50))))&(X48!=X50|~r2_hidden(X48,k4_xboole_0(X49,k1_tarski(X50)))))&(~r2_hidden(X48,X49)|X48=X50|r2_hidden(X48,k4_xboole_0(X49,k1_tarski(X50))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 1.19/1.36  cnf(c_0_111, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),esk3_0)), inference(spm,[status(thm)],[c_0_73, c_0_57])).
% 1.19/1.36  fof(c_0_112, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~r2_hidden(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 1.19/1.36  cnf(c_0_113, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|k4_xboole_0(k4_xboole_0(X1,X2),X3)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_94, c_0_58])).
% 1.19/1.36  cnf(c_0_114, negated_conjecture, (k4_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_109])).
% 1.19/1.36  cnf(c_0_115, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_110])).
% 1.19/1.36  cnf(c_0_116, negated_conjecture, (r1_tarski(esk2_0,esk3_0)|r2_hidden(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_111, c_0_67])).
% 1.19/1.36  cnf(c_0_117, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_112])).
% 1.19/1.36  cnf(c_0_118, negated_conjecture, (r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_78])])).
% 1.19/1.36  cnf(c_0_119, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_34]), c_0_29]), c_0_39]), c_0_40])).
% 1.19/1.36  cnf(c_0_120, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=k1_xboole_0|r2_hidden(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_56, c_0_116])).
% 1.19/1.36  cnf(c_0_121, negated_conjecture, (~r2_hidden(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_117, c_0_107])).
% 1.19/1.36  cnf(c_0_122, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_86, c_0_77])).
% 1.19/1.36  cnf(c_0_123, plain, (~r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X4,X2),X3))), inference(spm,[status(thm)],[c_0_86, c_0_58])).
% 1.19/1.36  cnf(c_0_124, negated_conjecture, (r2_hidden(esk2_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)))), inference(spm,[status(thm)],[c_0_87, c_0_118])).
% 1.19/1.36  fof(c_0_125, plain, ![X54]:r2_hidden(X54,k1_ordinal1(X54)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 1.19/1.36  cnf(c_0_126, plain, (~r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)))), inference(er,[status(thm)],[c_0_119])).
% 1.19/1.36  cnf(c_0_127, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk3_0),esk2_0)=k4_xboole_0(X1,esk3_0)|r2_hidden(esk3_0,k4_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_58, c_0_90])).
% 1.19/1.36  cnf(c_0_128, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_120, c_0_121])).
% 1.19/1.36  cnf(c_0_129, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_77]), c_0_122])).
% 1.19/1.36  cnf(c_0_130, negated_conjecture, (~r2_hidden(esk2_0,k4_xboole_0(k4_xboole_0(X1,esk3_0),X2))), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 1.19/1.36  cnf(c_0_131, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_61]), c_0_61])).
% 1.19/1.36  cnf(c_0_132, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.19/1.36  cnf(c_0_133, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_125])).
% 1.19/1.36  cnf(c_0_134, negated_conjecture, (r2_hidden(esk2_0,k4_xboole_0(X1,esk2_0))|~r2_hidden(esk3_0,k4_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_126, c_0_76])).
% 1.19/1.36  cnf(c_0_135, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk3_0),esk2_0)=k4_xboole_0(X1,esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_128]), c_0_129])).
% 1.19/1.36  cnf(c_0_136, negated_conjecture, (~r2_hidden(esk2_0,k4_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_130, c_0_131])).
% 1.19/1.36  cnf(c_0_137, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_132])).
% 1.19/1.36  cnf(c_0_138, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133, c_0_42]), c_0_29]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 1.19/1.36  cnf(c_0_139, negated_conjecture, (~r2_hidden(esk3_0,k4_xboole_0(X1,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_136])).
% 1.19/1.36  cnf(c_0_140, plain, (r2_hidden(X1,k4_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1))),X2))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 1.19/1.36  cnf(c_0_141, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_100, c_0_68])).
% 1.19/1.36  cnf(c_0_142, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_141]), ['proof']).
% 1.19/1.36  # SZS output end CNFRefutation
% 1.19/1.36  # Proof object total steps             : 143
% 1.19/1.36  # Proof object clause steps            : 98
% 1.19/1.36  # Proof object formula steps           : 45
% 1.19/1.36  # Proof object conjectures             : 40
% 1.19/1.36  # Proof object clause conjectures      : 37
% 1.19/1.36  # Proof object formula conjectures     : 3
% 1.19/1.36  # Proof object initial clauses used    : 27
% 1.19/1.36  # Proof object initial formulas used   : 22
% 1.19/1.36  # Proof object generating inferences   : 49
% 1.19/1.36  # Proof object simplifying inferences  : 86
% 1.19/1.36  # Training examples: 0 positive, 0 negative
% 1.19/1.36  # Parsed axioms                        : 22
% 1.19/1.36  # Removed by relevancy pruning/SinE    : 0
% 1.19/1.36  # Initial clauses                      : 36
% 1.19/1.36  # Removed in clause preprocessing      : 6
% 1.19/1.36  # Initial clauses in saturation        : 30
% 1.19/1.36  # Processed clauses                    : 4401
% 1.19/1.36  # ...of these trivial                  : 135
% 1.19/1.36  # ...subsumed                          : 3639
% 1.19/1.36  # ...remaining for further processing  : 627
% 1.19/1.36  # Other redundant clauses eliminated   : 689
% 1.19/1.36  # Clauses deleted for lack of memory   : 0
% 1.19/1.36  # Backward-subsumed                    : 17
% 1.19/1.36  # Backward-rewritten                   : 79
% 1.19/1.36  # Generated clauses                    : 98880
% 1.19/1.36  # ...of the previous two non-trivial   : 91039
% 1.19/1.36  # Contextual simplify-reflections      : 6
% 1.19/1.36  # Paramodulations                      : 98168
% 1.19/1.36  # Factorizations                       : 12
% 1.19/1.36  # Equation resolutions                 : 689
% 1.19/1.36  # Propositional unsat checks           : 0
% 1.19/1.36  #    Propositional check models        : 0
% 1.19/1.36  #    Propositional check unsatisfiable : 0
% 1.19/1.36  #    Propositional clauses             : 0
% 1.19/1.36  #    Propositional clauses after purity: 0
% 1.19/1.36  #    Propositional unsat core size     : 0
% 1.19/1.36  #    Propositional preprocessing time  : 0.000
% 1.19/1.36  #    Propositional encoding time       : 0.000
% 1.19/1.36  #    Propositional solver time         : 0.000
% 1.19/1.36  #    Success case prop preproc time    : 0.000
% 1.19/1.36  #    Success case prop encoding time   : 0.000
% 1.19/1.36  #    Success case prop solver time     : 0.000
% 1.19/1.36  # Current number of processed clauses  : 486
% 1.19/1.36  #    Positive orientable unit clauses  : 93
% 1.19/1.36  #    Positive unorientable unit clauses: 2
% 1.19/1.36  #    Negative unit clauses             : 88
% 1.19/1.36  #    Non-unit-clauses                  : 303
% 1.19/1.36  # Current number of unprocessed clauses: 86342
% 1.19/1.36  # ...number of literals in the above   : 313939
% 1.19/1.36  # Current number of archived formulas  : 0
% 1.19/1.36  # Current number of archived clauses   : 141
% 1.19/1.36  # Clause-clause subsumption calls (NU) : 8634
% 1.19/1.36  # Rec. Clause-clause subsumption calls : 6713
% 1.19/1.36  # Non-unit clause-clause subsumptions  : 733
% 1.19/1.36  # Unit Clause-clause subsumption calls : 2247
% 1.19/1.36  # Rewrite failures with RHS unbound    : 0
% 1.19/1.36  # BW rewrite match attempts            : 408
% 1.19/1.36  # BW rewrite match successes           : 120
% 1.19/1.36  # Condensation attempts                : 0
% 1.19/1.36  # Condensation successes               : 0
% 1.19/1.36  # Termbank termtop insertions          : 2291158
% 1.19/1.36  
% 1.19/1.36  # -------------------------------------------------
% 1.19/1.36  # User time                : 0.983 s
% 1.19/1.36  # System time              : 0.039 s
% 1.19/1.36  # Total time               : 1.022 s
% 1.19/1.36  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
