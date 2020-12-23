%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:33 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 (1751 expanded)
%              Number of clauses        :   61 ( 829 expanded)
%              Number of leaves         :   18 ( 463 expanded)
%              Depth                    :   18
%              Number of atoms          :  170 (3031 expanded)
%              Number of equality atoms :   92 (1782 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t50_zfmisc_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_18,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_19,plain,(
    ! [X18,X19] :
      ( ( k4_xboole_0(X18,X19) != k1_xboole_0
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | k4_xboole_0(X18,X19) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_20,plain,(
    ! [X20,X21] : k4_xboole_0(X20,X21) = k5_xboole_0(X20,k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k3_xboole_0(X22,X23) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X55,X56] : k3_tarski(k2_tarski(X55,X56)) = k2_xboole_0(X55,X56) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X41,X42] : k1_enumset1(X41,X41,X42) = k2_tarski(X41,X42) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_29,plain,(
    ! [X27,X28,X29] : k5_xboole_0(k5_xboole_0(X27,X28),X29) = k5_xboole_0(X27,k5_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_32,plain,(
    ! [X30,X31] : k2_xboole_0(X30,X31) = k5_xboole_0(k5_xboole_0(X30,X31),k3_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_33,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X43,X44,X45] : k2_enumset1(X43,X43,X44,X45) = k1_enumset1(X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_36,plain,(
    ! [X46,X47,X48,X49] : k3_enumset1(X46,X46,X47,X48,X49) = k2_enumset1(X46,X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_37,plain,(
    ! [X50,X51,X52,X53,X54] : k4_enumset1(X50,X50,X51,X52,X53,X54) = k3_enumset1(X50,X51,X52,X53,X54) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t50_zfmisc_1])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_31])).

fof(c_0_41,plain,(
    ! [X24] : k5_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_47,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).

fof(c_0_48,plain,(
    ! [X25,X26] : r1_tarski(X25,k2_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_50])).

cnf(c_0_55,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_39])).

cnf(c_0_56,negated_conjecture,
    ( k3_tarski(k4_enumset1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_34]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_58,plain,
    ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_59,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_60,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_49,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k5_xboole_0(esk6_0,k3_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_63,plain,
    ( r1_tarski(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_68,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) = k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_50])).

cnf(c_0_69,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_63])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_64])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_24])).

cnf(c_0_73,negated_conjecture,
    ( k3_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0) = k5_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_68])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_75,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_76,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_50]),c_0_71])).

fof(c_0_77,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38,X39] :
      ( ( ~ r2_hidden(X35,X34)
        | X35 = X32
        | X35 = X33
        | X34 != k2_tarski(X32,X33) )
      & ( X36 != X32
        | r2_hidden(X36,X34)
        | X34 != k2_tarski(X32,X33) )
      & ( X36 != X33
        | r2_hidden(X36,X34)
        | X34 != k2_tarski(X32,X33) )
      & ( esk3_3(X37,X38,X39) != X37
        | ~ r2_hidden(esk3_3(X37,X38,X39),X39)
        | X39 = k2_tarski(X37,X38) )
      & ( esk3_3(X37,X38,X39) != X38
        | ~ r2_hidden(esk3_3(X37,X38,X39),X39)
        | X39 = k2_tarski(X37,X38) )
      & ( r2_hidden(esk3_3(X37,X38,X39),X39)
        | esk3_3(X37,X38,X39) = X37
        | esk3_3(X37,X38,X39) = X38
        | X39 = k2_tarski(X37,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)
    | k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k5_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_74]),c_0_50])).

cnf(c_0_80,plain,
    ( X1 = X2
    | r2_hidden(esk2_2(X2,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_64])).

cnf(c_0_81,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_76]),c_0_50])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)
    | esk6_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_84,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk2_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X2,X2,X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_34]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k1_xboole_0)
    | r2_hidden(esk2_2(esk6_0,k1_xboole_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_85])])).

cnf(c_0_88,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) = k1_xboole_0
    | r2_hidden(esk2_2(esk6_0,k1_xboole_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_86]),c_0_81])])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_55])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk2_2(esk6_0,k1_xboole_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_71])).

cnf(c_0_91,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk2_2(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k1_xboole_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_84]),c_0_76]),c_0_50])).

cnf(c_0_92,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_73]),c_0_61]),c_0_40])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk2_2(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k1_xboole_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_71])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_hidden(X1,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_71])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_94,c_0_95]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.43  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.21/0.43  # and selection function SelectNegativeLiterals.
% 0.21/0.43  #
% 0.21/0.43  # Preprocessing time       : 0.037 s
% 0.21/0.43  # Presaturation interreduction done
% 0.21/0.43  
% 0.21/0.43  # Proof found!
% 0.21/0.43  # SZS status Theorem
% 0.21/0.43  # SZS output start CNFRefutation
% 0.21/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.43  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.21/0.43  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.43  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.43  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.43  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.21/0.43  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.21/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.43  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.43  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.21/0.43  fof(t50_zfmisc_1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 0.21/0.43  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.21/0.43  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.21/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.43  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.43  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.21/0.43  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.21/0.43  fof(c_0_18, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.43  fof(c_0_19, plain, ![X18, X19]:((k4_xboole_0(X18,X19)!=k1_xboole_0|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|k4_xboole_0(X18,X19)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.21/0.43  fof(c_0_20, plain, ![X20, X21]:k4_xboole_0(X20,X21)=k5_xboole_0(X20,k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.43  fof(c_0_21, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k3_xboole_0(X22,X23)=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.43  cnf(c_0_22, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.43  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.43  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.43  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.43  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.21/0.43  fof(c_0_27, plain, ![X55, X56]:k3_tarski(k2_tarski(X55,X56))=k2_xboole_0(X55,X56), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.43  fof(c_0_28, plain, ![X41, X42]:k1_enumset1(X41,X41,X42)=k2_tarski(X41,X42), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.43  fof(c_0_29, plain, ![X27, X28, X29]:k5_xboole_0(k5_xboole_0(X27,X28),X29)=k5_xboole_0(X27,k5_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.21/0.43  cnf(c_0_30, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.43  cnf(c_0_31, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.43  fof(c_0_32, plain, ![X30, X31]:k2_xboole_0(X30,X31)=k5_xboole_0(k5_xboole_0(X30,X31),k3_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.21/0.43  cnf(c_0_33, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.43  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.43  fof(c_0_35, plain, ![X43, X44, X45]:k2_enumset1(X43,X43,X44,X45)=k1_enumset1(X43,X44,X45), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.43  fof(c_0_36, plain, ![X46, X47, X48, X49]:k3_enumset1(X46,X46,X47,X48,X49)=k2_enumset1(X46,X47,X48,X49), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.43  fof(c_0_37, plain, ![X50, X51, X52, X53, X54]:k4_enumset1(X50,X50,X51,X52,X53,X54)=k3_enumset1(X50,X51,X52,X53,X54), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.21/0.43  fof(c_0_38, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t50_zfmisc_1])).
% 0.21/0.43  cnf(c_0_39, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.43  cnf(c_0_40, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_26]), c_0_31])).
% 0.21/0.43  fof(c_0_41, plain, ![X24]:k5_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.21/0.43  cnf(c_0_42, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.43  cnf(c_0_43, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.43  cnf(c_0_44, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.43  cnf(c_0_45, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.43  cnf(c_0_46, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.43  fof(c_0_47, negated_conjecture, k2_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).
% 0.21/0.43  fof(c_0_48, plain, ![X25, X26]:r1_tarski(X25,k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.21/0.43  cnf(c_0_49, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.43  cnf(c_0_50, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.43  cnf(c_0_51, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.21/0.43  cnf(c_0_52, negated_conjecture, (k2_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.43  cnf(c_0_53, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.43  cnf(c_0_54, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_40]), c_0_50])).
% 0.21/0.43  cnf(c_0_55, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_51, c_0_39])).
% 0.21/0.43  cnf(c_0_56, negated_conjecture, (k3_tarski(k4_enumset1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_34]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 0.21/0.43  cnf(c_0_57, plain, (r1_tarski(X1,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.21/0.43  cnf(c_0_58, plain, (k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.43  fof(c_0_59, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.43  fof(c_0_60, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.43  cnf(c_0_61, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_49, c_0_54])).
% 0.21/0.43  cnf(c_0_62, negated_conjecture, (k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k5_xboole_0(esk6_0,k3_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_56, c_0_55])).
% 0.21/0.43  cnf(c_0_63, plain, (r1_tarski(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.21/0.43  cnf(c_0_64, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.43  cnf(c_0_65, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.21/0.43  cnf(c_0_66, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.21/0.43  cnf(c_0_67, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.43  cnf(c_0_68, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))=k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_50])).
% 0.21/0.43  cnf(c_0_69, plain, (k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_63])).
% 0.21/0.43  cnf(c_0_70, plain, (k3_xboole_0(X1,X2)=X1|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_25, c_0_64])).
% 0.21/0.43  cnf(c_0_71, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.21/0.43  cnf(c_0_72, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_67, c_0_24])).
% 0.21/0.43  cnf(c_0_73, negated_conjecture, (k3_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)=k5_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_61, c_0_68])).
% 0.21/0.43  cnf(c_0_74, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.43  cnf(c_0_75, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.43  cnf(c_0_76, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_50]), c_0_71])).
% 0.21/0.43  fof(c_0_77, plain, ![X32, X33, X34, X35, X36, X37, X38, X39]:(((~r2_hidden(X35,X34)|(X35=X32|X35=X33)|X34!=k2_tarski(X32,X33))&((X36!=X32|r2_hidden(X36,X34)|X34!=k2_tarski(X32,X33))&(X36!=X33|r2_hidden(X36,X34)|X34!=k2_tarski(X32,X33))))&(((esk3_3(X37,X38,X39)!=X37|~r2_hidden(esk3_3(X37,X38,X39),X39)|X39=k2_tarski(X37,X38))&(esk3_3(X37,X38,X39)!=X38|~r2_hidden(esk3_3(X37,X38,X39),X39)|X39=k2_tarski(X37,X38)))&(r2_hidden(esk3_3(X37,X38,X39),X39)|(esk3_3(X37,X38,X39)=X37|esk3_3(X37,X38,X39)=X38)|X39=k2_tarski(X37,X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.21/0.43  cnf(c_0_78, negated_conjecture, (r1_tarski(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)|k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k5_xboole_0(esk6_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.21/0.43  cnf(c_0_79, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_74]), c_0_50])).
% 0.21/0.43  cnf(c_0_80, plain, (X1=X2|r2_hidden(esk2_2(X2,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_75, c_0_64])).
% 0.21/0.43  cnf(c_0_81, plain, (r1_tarski(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_76]), c_0_50])).
% 0.21/0.43  cnf(c_0_82, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.21/0.43  cnf(c_0_83, negated_conjecture, (r1_tarski(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)|esk6_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_78, c_0_79])).
% 0.21/0.43  cnf(c_0_84, plain, (k1_xboole_0=X1|r2_hidden(esk2_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.21/0.43  cnf(c_0_85, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X2,X2,X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_34]), c_0_44]), c_0_45]), c_0_46])).
% 0.21/0.43  cnf(c_0_86, negated_conjecture, (r1_tarski(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k1_xboole_0)|r2_hidden(esk2_2(esk6_0,k1_xboole_0),esk6_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.21/0.43  cnf(c_0_87, plain, (r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_85])])).
% 0.21/0.43  cnf(c_0_88, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)=k1_xboole_0|r2_hidden(esk2_2(esk6_0,k1_xboole_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_86]), c_0_81])])).
% 0.21/0.43  cnf(c_0_89, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_57, c_0_55])).
% 0.21/0.43  cnf(c_0_90, negated_conjecture, (r2_hidden(esk2_2(esk6_0,k1_xboole_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_71])).
% 0.21/0.43  cnf(c_0_91, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk2_2(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k1_xboole_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_84]), c_0_76]), c_0_50])).
% 0.21/0.43  cnf(c_0_92, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.21/0.43  cnf(c_0_93, negated_conjecture, (r1_tarski(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_73]), c_0_61]), c_0_40])).
% 0.21/0.43  cnf(c_0_94, negated_conjecture, (r2_hidden(esk2_2(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k1_xboole_0),k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_71])).
% 0.21/0.43  cnf(c_0_95, negated_conjecture, (~r2_hidden(X1,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_71])).
% 0.21/0.43  cnf(c_0_96, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_94, c_0_95]), ['proof']).
% 0.21/0.43  # SZS output end CNFRefutation
% 0.21/0.43  # Proof object total steps             : 97
% 0.21/0.43  # Proof object clause steps            : 61
% 0.21/0.43  # Proof object formula steps           : 36
% 0.21/0.43  # Proof object conjectures             : 18
% 0.21/0.43  # Proof object clause conjectures      : 15
% 0.21/0.43  # Proof object formula conjectures     : 3
% 0.21/0.43  # Proof object initial clauses used    : 21
% 0.21/0.43  # Proof object initial formulas used   : 18
% 0.21/0.43  # Proof object generating inferences   : 25
% 0.21/0.43  # Proof object simplifying inferences  : 54
% 0.21/0.43  # Training examples: 0 positive, 0 negative
% 0.21/0.43  # Parsed axioms                        : 18
% 0.21/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.43  # Initial clauses                      : 29
% 0.21/0.43  # Removed in clause preprocessing      : 6
% 0.21/0.43  # Initial clauses in saturation        : 23
% 0.21/0.43  # Processed clauses                    : 239
% 0.21/0.43  # ...of these trivial                  : 16
% 0.21/0.43  # ...subsumed                          : 80
% 0.21/0.43  # ...remaining for further processing  : 143
% 0.21/0.43  # Other redundant clauses eliminated   : 59
% 0.21/0.43  # Clauses deleted for lack of memory   : 0
% 0.21/0.43  # Backward-subsumed                    : 4
% 0.21/0.43  # Backward-rewritten                   : 21
% 0.21/0.43  # Generated clauses                    : 1575
% 0.21/0.43  # ...of the previous two non-trivial   : 1294
% 0.21/0.43  # Contextual simplify-reflections      : 1
% 0.21/0.43  # Paramodulations                      : 1504
% 0.21/0.43  # Factorizations                       : 12
% 0.21/0.43  # Equation resolutions                 : 59
% 0.21/0.43  # Propositional unsat checks           : 0
% 0.21/0.43  #    Propositional check models        : 0
% 0.21/0.43  #    Propositional check unsatisfiable : 0
% 0.21/0.43  #    Propositional clauses             : 0
% 0.21/0.43  #    Propositional clauses after purity: 0
% 0.21/0.43  #    Propositional unsat core size     : 0
% 0.21/0.43  #    Propositional preprocessing time  : 0.000
% 0.21/0.43  #    Propositional encoding time       : 0.000
% 0.21/0.43  #    Propositional solver time         : 0.000
% 0.21/0.43  #    Success case prop preproc time    : 0.000
% 0.21/0.43  #    Success case prop encoding time   : 0.000
% 0.21/0.43  #    Success case prop solver time     : 0.000
% 0.21/0.43  # Current number of processed clauses  : 89
% 0.21/0.43  #    Positive orientable unit clauses  : 27
% 0.21/0.43  #    Positive unorientable unit clauses: 5
% 0.21/0.43  #    Negative unit clauses             : 2
% 0.21/0.43  #    Non-unit-clauses                  : 55
% 0.21/0.43  # Current number of unprocessed clauses: 1049
% 0.21/0.43  # ...number of literals in the above   : 2576
% 0.21/0.43  # Current number of archived formulas  : 0
% 0.21/0.43  # Current number of archived clauses   : 55
% 0.21/0.43  # Clause-clause subsumption calls (NU) : 460
% 0.21/0.43  # Rec. Clause-clause subsumption calls : 421
% 0.21/0.43  # Non-unit clause-clause subsumptions  : 73
% 0.21/0.43  # Unit Clause-clause subsumption calls : 24
% 0.21/0.43  # Rewrite failures with RHS unbound    : 0
% 0.21/0.43  # BW rewrite match attempts            : 89
% 0.21/0.43  # BW rewrite match successes           : 51
% 0.21/0.43  # Condensation attempts                : 0
% 0.21/0.43  # Condensation successes               : 0
% 0.21/0.43  # Termbank termtop insertions          : 21045
% 0.21/0.43  
% 0.21/0.43  # -------------------------------------------------
% 0.21/0.43  # User time                : 0.081 s
% 0.21/0.43  # System time              : 0.006 s
% 0.21/0.43  # Total time               : 0.087 s
% 0.21/0.43  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
