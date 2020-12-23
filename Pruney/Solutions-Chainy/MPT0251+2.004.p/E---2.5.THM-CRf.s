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
% DateTime   : Thu Dec  3 10:40:22 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 573 expanded)
%              Number of clauses        :   46 ( 235 expanded)
%              Number of leaves         :   19 ( 167 expanded)
%              Depth                    :   11
%              Number of atoms          :  160 ( 746 expanded)
%              Number of equality atoms :   64 ( 532 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t46_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t88_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(c_0_19,plain,(
    ! [X52,X53] :
      ( ( ~ r1_tarski(k1_tarski(X52),X53)
        | r2_hidden(X52,X53) )
      & ( ~ r2_hidden(X52,X53)
        | r1_tarski(k1_tarski(X52),X53) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_20,plain,(
    ! [X42] : k2_tarski(X42,X42) = k1_tarski(X42) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X43,X44] : k1_enumset1(X43,X43,X44) = k2_tarski(X43,X44) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X45,X46,X47] : k2_enumset1(X45,X45,X46,X47) = k1_enumset1(X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X48,X49,X50,X51] : k3_enumset1(X48,X48,X49,X50,X51) = k2_enumset1(X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t46_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X54,X55] : k3_tarski(k2_tarski(X54,X55)) = k2_xboole_0(X54,X55) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    & k2_xboole_0(k1_tarski(esk4_0),esk5_0) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_32,plain,(
    ! [X38,X39] :
      ( ~ r1_xboole_0(X38,X39)
      | k4_xboole_0(k2_xboole_0(X38,X39),X39) = X38 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).

cnf(c_0_33,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_34,plain,(
    ! [X30,X31] : k4_xboole_0(X30,X31) = k5_xboole_0(X30,k3_xboole_0(X30,X31)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_35,plain,(
    ! [X32] : k2_xboole_0(X32,k1_xboole_0) = X32 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_36,plain,(
    ! [X40,X41] : k2_tarski(X40,X41) = k2_tarski(X41,X40) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_37,plain,(
    ! [X28,X29] :
      ( ( r1_tarski(X28,X29)
        | X28 != X29 )
      & ( r1_tarski(X29,X28)
        | X28 != X29 )
      & ( ~ r1_tarski(X28,X29)
        | ~ r1_tarski(X29,X28)
        | X28 = X29 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_38,plain,(
    ! [X36,X37] : k2_xboole_0(X36,k4_xboole_0(X37,X36)) = k2_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_39,plain,(
    ! [X33,X34] :
      ( ~ r1_tarski(X33,X34)
      | k3_xboole_0(X33,X34) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_40,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_28])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_45,plain,(
    ! [X22,X23,X25,X26,X27] :
      ( ( r2_hidden(esk3_2(X22,X23),X22)
        | r1_xboole_0(X22,X23) )
      & ( r2_hidden(esk3_2(X22,X23),X23)
        | r1_xboole_0(X22,X23) )
      & ( ~ r2_hidden(X27,X25)
        | ~ r2_hidden(X27,X26)
        | ~ r1_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_29]),c_0_29]),c_0_30]),c_0_30])).

cnf(c_0_53,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_43]),c_0_29]),c_0_30])).

cnf(c_0_55,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk4_0),esk5_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_58,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_59,plain,(
    ! [X35] : r1_tarski(k1_xboole_0,X35) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_60,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_61,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_43]),c_0_43]),c_0_44]),c_0_29]),c_0_29]),c_0_30]),c_0_30])).

cnf(c_0_62,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_63,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X2)) = X1
    | r2_hidden(esk3_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_64,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_50,c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_27]),c_0_28]),c_0_43]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) = k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,X1),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_66,c_0_55])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_68])).

cnf(c_0_76,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_55]),c_0_64]),c_0_73])).

fof(c_0_78,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk1_1(k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk1_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( ~ r2_hidden(X1,esk1_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_83,c_0_82]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.77/0.95  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.77/0.95  # and selection function SelectNegativeLiterals.
% 0.77/0.95  #
% 0.77/0.95  # Preprocessing time       : 0.042 s
% 0.77/0.95  # Presaturation interreduction done
% 0.77/0.95  
% 0.77/0.95  # Proof found!
% 0.77/0.95  # SZS status Theorem
% 0.77/0.95  # SZS output start CNFRefutation
% 0.77/0.95  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.77/0.95  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.77/0.95  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.77/0.95  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.77/0.95  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.77/0.95  fof(t46_zfmisc_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 0.77/0.95  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.77/0.95  fof(t88_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 0.77/0.95  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.77/0.95  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.77/0.95  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.77/0.95  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.77/0.95  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.77/0.95  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.77/0.95  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.77/0.95  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.77/0.95  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.77/0.95  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.77/0.95  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.77/0.95  fof(c_0_19, plain, ![X52, X53]:((~r1_tarski(k1_tarski(X52),X53)|r2_hidden(X52,X53))&(~r2_hidden(X52,X53)|r1_tarski(k1_tarski(X52),X53))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.77/0.95  fof(c_0_20, plain, ![X42]:k2_tarski(X42,X42)=k1_tarski(X42), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.77/0.95  fof(c_0_21, plain, ![X43, X44]:k1_enumset1(X43,X43,X44)=k2_tarski(X43,X44), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.77/0.95  fof(c_0_22, plain, ![X45, X46, X47]:k2_enumset1(X45,X45,X46,X47)=k1_enumset1(X45,X46,X47), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.77/0.95  fof(c_0_23, plain, ![X48, X49, X50, X51]:k3_enumset1(X48,X48,X49,X50,X51)=k2_enumset1(X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.77/0.95  fof(c_0_24, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2)), inference(assume_negation,[status(cth)],[t46_zfmisc_1])).
% 0.77/0.95  fof(c_0_25, plain, ![X54, X55]:k3_tarski(k2_tarski(X54,X55))=k2_xboole_0(X54,X55), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.77/0.95  cnf(c_0_26, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.77/0.95  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.77/0.95  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.77/0.95  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.77/0.95  cnf(c_0_30, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.77/0.95  fof(c_0_31, negated_conjecture, (r2_hidden(esk4_0,esk5_0)&k2_xboole_0(k1_tarski(esk4_0),esk5_0)!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.77/0.95  fof(c_0_32, plain, ![X38, X39]:(~r1_xboole_0(X38,X39)|k4_xboole_0(k2_xboole_0(X38,X39),X39)=X38), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).
% 0.77/0.95  cnf(c_0_33, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.77/0.95  fof(c_0_34, plain, ![X30, X31]:k4_xboole_0(X30,X31)=k5_xboole_0(X30,k3_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.77/0.95  fof(c_0_35, plain, ![X32]:k2_xboole_0(X32,k1_xboole_0)=X32, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.77/0.95  fof(c_0_36, plain, ![X40, X41]:k2_tarski(X40,X41)=k2_tarski(X41,X40), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.77/0.95  fof(c_0_37, plain, ![X28, X29]:(((r1_tarski(X28,X29)|X28!=X29)&(r1_tarski(X29,X28)|X28!=X29))&(~r1_tarski(X28,X29)|~r1_tarski(X29,X28)|X28=X29)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.77/0.95  fof(c_0_38, plain, ![X36, X37]:k2_xboole_0(X36,k4_xboole_0(X37,X36))=k2_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.77/0.95  fof(c_0_39, plain, ![X33, X34]:(~r1_tarski(X33,X34)|k3_xboole_0(X33,X34)=X33), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.77/0.95  cnf(c_0_40, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.77/0.95  cnf(c_0_41, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.77/0.95  cnf(c_0_42, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.77/0.95  cnf(c_0_43, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_28])).
% 0.77/0.95  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.77/0.95  fof(c_0_45, plain, ![X22, X23, X25, X26, X27]:(((r2_hidden(esk3_2(X22,X23),X22)|r1_xboole_0(X22,X23))&(r2_hidden(esk3_2(X22,X23),X23)|r1_xboole_0(X22,X23)))&(~r2_hidden(X27,X25)|~r2_hidden(X27,X26)|~r1_xboole_0(X25,X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.77/0.95  cnf(c_0_46, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.77/0.95  cnf(c_0_47, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.77/0.95  cnf(c_0_48, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.77/0.95  cnf(c_0_49, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.77/0.95  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.77/0.95  cnf(c_0_51, negated_conjecture, (r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.77/0.95  cnf(c_0_52, plain, (k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_29]), c_0_29]), c_0_30]), c_0_30])).
% 0.77/0.95  cnf(c_0_53, plain, (r2_hidden(esk3_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.77/0.95  cnf(c_0_54, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_43]), c_0_29]), c_0_30])).
% 0.77/0.95  cnf(c_0_55, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30])).
% 0.77/0.95  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_48])).
% 0.77/0.95  cnf(c_0_57, negated_conjecture, (k2_xboole_0(k1_tarski(esk4_0),esk5_0)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.77/0.95  fof(c_0_58, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.77/0.95  fof(c_0_59, plain, ![X35]:r1_tarski(k1_xboole_0,X35), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.77/0.95  fof(c_0_60, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.77/0.95  cnf(c_0_61, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_43]), c_0_43]), c_0_44]), c_0_29]), c_0_29]), c_0_30]), c_0_30])).
% 0.77/0.95  cnf(c_0_62, negated_conjecture, (k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.77/0.95  cnf(c_0_63, plain, (k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X2))=X1|r2_hidden(esk3_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.77/0.95  cnf(c_0_64, plain, (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.77/0.95  cnf(c_0_65, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_50, c_0_56])).
% 0.77/0.95  cnf(c_0_66, negated_conjecture, (k3_tarski(k3_enumset1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_27]), c_0_28]), c_0_43]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.77/0.95  cnf(c_0_67, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.77/0.95  cnf(c_0_68, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.77/0.95  cnf(c_0_69, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.77/0.95  cnf(c_0_70, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.77/0.95  cnf(c_0_71, negated_conjecture, (k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))=k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.77/0.95  cnf(c_0_72, plain, (k5_xboole_0(X1,X1)=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,X1),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.77/0.95  cnf(c_0_73, negated_conjecture, (k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))!=esk5_0), inference(rw,[status(thm)],[c_0_66, c_0_55])).
% 0.77/0.95  cnf(c_0_74, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_67])).
% 0.77/0.95  cnf(c_0_75, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_68])).
% 0.77/0.95  cnf(c_0_76, plain, (r2_hidden(esk1_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.77/0.95  cnf(c_0_77, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k1_xboole_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_55]), c_0_64]), c_0_73])).
% 0.77/0.95  fof(c_0_78, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~r2_hidden(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.77/0.95  cnf(c_0_79, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.77/0.95  cnf(c_0_80, negated_conjecture, (r2_hidden(esk1_1(k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.77/0.95  cnf(c_0_81, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.77/0.95  cnf(c_0_82, negated_conjecture, (r2_hidden(esk1_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.77/0.95  cnf(c_0_83, negated_conjecture, (~r2_hidden(X1,esk1_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.77/0.95  cnf(c_0_84, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_83, c_0_82]), ['proof']).
% 0.77/0.95  # SZS output end CNFRefutation
% 0.77/0.95  # Proof object total steps             : 85
% 0.77/0.95  # Proof object clause steps            : 46
% 0.77/0.95  # Proof object formula steps           : 39
% 0.77/0.95  # Proof object conjectures             : 15
% 0.77/0.95  # Proof object clause conjectures      : 12
% 0.77/0.95  # Proof object formula conjectures     : 3
% 0.77/0.95  # Proof object initial clauses used    : 21
% 0.77/0.95  # Proof object initial formulas used   : 19
% 0.77/0.95  # Proof object generating inferences   : 15
% 0.77/0.95  # Proof object simplifying inferences  : 44
% 0.77/0.95  # Training examples: 0 positive, 0 negative
% 0.77/0.95  # Parsed axioms                        : 20
% 0.77/0.95  # Removed by relevancy pruning/SinE    : 0
% 0.77/0.95  # Initial clauses                      : 32
% 0.77/0.95  # Removed in clause preprocessing      : 6
% 0.77/0.95  # Initial clauses in saturation        : 26
% 0.77/0.95  # Processed clauses                    : 1476
% 0.77/0.95  # ...of these trivial                  : 112
% 0.77/0.95  # ...subsumed                          : 719
% 0.77/0.95  # ...remaining for further processing  : 645
% 0.77/0.95  # Other redundant clauses eliminated   : 132
% 0.77/0.95  # Clauses deleted for lack of memory   : 0
% 0.77/0.95  # Backward-subsumed                    : 10
% 0.77/0.95  # Backward-rewritten                   : 14
% 0.77/0.95  # Generated clauses                    : 52602
% 0.77/0.95  # ...of the previous two non-trivial   : 48433
% 0.77/0.95  # Contextual simplify-reflections      : 6
% 0.77/0.95  # Paramodulations                      : 52462
% 0.77/0.95  # Factorizations                       : 8
% 0.77/0.95  # Equation resolutions                 : 132
% 0.77/0.95  # Propositional unsat checks           : 0
% 0.77/0.95  #    Propositional check models        : 0
% 0.77/0.95  #    Propositional check unsatisfiable : 0
% 0.77/0.95  #    Propositional clauses             : 0
% 0.77/0.95  #    Propositional clauses after purity: 0
% 0.77/0.95  #    Propositional unsat core size     : 0
% 0.77/0.95  #    Propositional preprocessing time  : 0.000
% 0.77/0.95  #    Propositional encoding time       : 0.000
% 0.77/0.95  #    Propositional solver time         : 0.000
% 0.77/0.95  #    Success case prop preproc time    : 0.000
% 0.77/0.95  #    Success case prop encoding time   : 0.000
% 0.77/0.95  #    Success case prop solver time     : 0.000
% 0.77/0.95  # Current number of processed clauses  : 591
% 0.77/0.95  #    Positive orientable unit clauses  : 85
% 0.77/0.95  #    Positive unorientable unit clauses: 1
% 0.77/0.95  #    Negative unit clauses             : 51
% 0.77/0.95  #    Non-unit-clauses                  : 454
% 0.77/0.95  # Current number of unprocessed clauses: 46938
% 0.77/0.95  # ...number of literals in the above   : 211324
% 0.77/0.95  # Current number of archived formulas  : 0
% 0.77/0.95  # Current number of archived clauses   : 55
% 0.77/0.95  # Clause-clause subsumption calls (NU) : 32988
% 0.77/0.95  # Rec. Clause-clause subsumption calls : 22184
% 0.77/0.95  # Non-unit clause-clause subsumptions  : 501
% 0.77/0.95  # Unit Clause-clause subsumption calls : 3035
% 0.77/0.95  # Rewrite failures with RHS unbound    : 0
% 0.77/0.95  # BW rewrite match attempts            : 82
% 0.77/0.95  # BW rewrite match successes           : 27
% 0.77/0.95  # Condensation attempts                : 0
% 0.77/0.95  # Condensation successes               : 0
% 0.77/0.95  # Termbank termtop insertions          : 991231
% 0.77/0.96  
% 0.77/0.96  # -------------------------------------------------
% 0.77/0.96  # User time                : 0.580 s
% 0.77/0.96  # System time              : 0.029 s
% 0.77/0.96  # Total time               : 0.610 s
% 0.77/0.96  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
