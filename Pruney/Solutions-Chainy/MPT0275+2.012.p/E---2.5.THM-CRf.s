%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:02 EST 2020

% Result     : Theorem 4.93s
% Output     : CNFRefutation 4.93s
% Verified   : 
% Statistics : Number of formulae       :  149 (63625 expanded)
%              Number of clauses        :  104 (30252 expanded)
%              Number of leaves         :   22 (16684 expanded)
%              Depth                    :   26
%              Number of atoms          :  270 (88568 expanded)
%              Number of equality atoms :  116 (52521 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

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

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t73_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(t92_enumset1,axiom,(
    ! [X1,X2] : k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(t34_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))
    <=> ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_22,plain,(
    ! [X45,X46] : k2_xboole_0(X45,X46) = k5_xboole_0(k5_xboole_0(X45,X46),k3_xboole_0(X45,X46)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_23,plain,(
    ! [X36,X37] : k4_xboole_0(X36,k4_xboole_0(X36,X37)) = k3_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_24,plain,(
    ! [X38,X39] : k2_xboole_0(k3_xboole_0(X38,X39),k4_xboole_0(X38,X39)) = X38 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X24,X25,X26] : k4_xboole_0(X24,k3_xboole_0(X25,X26)) = k2_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,X26)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

fof(c_0_28,plain,(
    ! [X18,X19,X21,X22,X23] :
      ( ( r1_xboole_0(X18,X19)
        | r2_hidden(esk2_2(X18,X19),k3_xboole_0(X18,X19)) )
      & ( ~ r2_hidden(X23,k3_xboole_0(X21,X22))
        | ~ r1_xboole_0(X21,X22) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_29,plain,(
    ! [X10,X11] :
      ( ~ r1_xboole_0(X10,X11)
      | r1_xboole_0(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_30,plain,(
    ! [X41,X42] : r1_xboole_0(k4_xboole_0(X41,X42),X42) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_31,plain,(
    ! [X34,X35] : k4_xboole_0(X34,k3_xboole_0(X34,X35)) = k4_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_32,plain,(
    ! [X40] :
      ( ( r1_xboole_0(X40,X40)
        | X40 != k1_xboole_0 )
      & ( X40 = k1_xboole_0
        | ~ r1_xboole_0(X40,X40) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_33,plain,(
    ! [X12,X13,X15,X16,X17] :
      ( ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_2(X12,X13),X13)
        | r1_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | ~ r1_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_36,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_41,plain,(
    ! [X29,X30] : r1_tarski(k3_xboole_0(X29,X30),X29) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_26]),c_0_35])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_26]),c_0_35])).

cnf(c_0_48,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_26])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_50,plain,(
    ! [X31,X32,X33] : k4_xboole_0(k4_xboole_0(X31,X32),X33) = k4_xboole_0(X31,k2_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_51,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k2_xboole_0(X27,X28) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_26])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_52,c_0_26])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,X2)
    | r2_hidden(esk1_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_53])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_35])).

cnf(c_0_65,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_59,c_0_35])).

cnf(c_0_66,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_53])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k1_xboole_0),k5_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3)
    | r2_hidden(esk1_2(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)),k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_54]),c_0_46])).

cnf(c_0_69,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_46])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_67]),c_0_67]),c_0_67])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3)
    | r2_hidden(esk1_2(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)),k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_67])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_67]),c_0_70]),c_0_46])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_63])).

fof(c_0_74,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t73_zfmisc_1])).

cnf(c_0_75,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_64])).

cnf(c_0_76,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_62,c_0_73])).

fof(c_0_77,negated_conjecture,
    ( ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0
      | ~ r2_hidden(esk3_0,esk5_0)
      | ~ r2_hidden(esk4_0,esk5_0) )
    & ( r2_hidden(esk3_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 )
    & ( r2_hidden(esk4_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_74])])])])).

fof(c_0_78,plain,(
    ! [X54,X55] : k5_enumset1(X54,X54,X54,X54,X54,X54,X55) = k2_tarski(X54,X55) ),
    inference(variable_rename,[status(thm)],[t92_enumset1])).

fof(c_0_79,plain,(
    ! [X47,X48,X49,X50,X51,X52,X53] : k6_enumset1(X47,X47,X48,X49,X50,X51,X52,X53) = k5_enumset1(X47,X48,X49,X50,X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_80,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0))) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | r2_hidden(esk1_2(k4_xboole_0(X1,X3),k4_xboole_0(X1,X3)),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_54]),c_0_46])).

cnf(c_0_82,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_84,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_85,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_86,plain,(
    ! [X43,X44] : k2_xboole_0(X43,X44) = k2_xboole_0(k5_xboole_0(X43,X44),k3_xboole_0(X43,X44)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

cnf(c_0_87,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_64])).

cnf(c_0_88,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_80])).

cnf(c_0_89,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | r2_hidden(esk1_2(k4_xboole_0(X1,X3),k4_xboole_0(X1,X3)),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_67])).

cnf(c_0_90,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))) = k4_xboole_0(k1_xboole_0,X2)
    | r2_hidden(esk1_2(k4_xboole_0(X1,X3),k4_xboole_0(X1,X3)),k4_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_54])).

cnf(c_0_91,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_67])).

cnf(c_0_92,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_93,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_94,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_87]),c_0_46])).

cnf(c_0_95,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_88])).

cnf(c_0_96,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_67]),c_0_67]),c_0_67]),c_0_67]),c_0_46]),c_0_72]),c_0_91]),c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)),k4_xboole_0(k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1),k4_xboole_0(k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1),k1_xboole_0))) = k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))
    | r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_92]),c_0_46])).

cnf(c_0_98,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_26]),c_0_35]),c_0_35])).

cnf(c_0_99,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_46]),c_0_96]),c_0_67])).

fof(c_0_100,plain,(
    ! [X62,X63,X64,X65] :
      ( ( X62 = X64
        | ~ r2_hidden(k4_tarski(X62,X63),k2_zfmisc_1(k1_tarski(X64),k1_tarski(X65))) )
      & ( X63 = X65
        | ~ r2_hidden(k4_tarski(X62,X63),k2_zfmisc_1(k1_tarski(X64),k1_tarski(X65))) )
      & ( X62 != X64
        | X63 != X65
        | r2_hidden(k4_tarski(X62,X63),k2_zfmisc_1(k1_tarski(X64),k1_tarski(X65))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).

fof(c_0_101,plain,(
    ! [X66,X67,X68] :
      ( ( ~ r2_hidden(X66,X68)
        | k4_xboole_0(k2_tarski(X66,X67),X68) != k2_tarski(X66,X67) )
      & ( ~ r2_hidden(X67,X68)
        | k4_xboole_0(k2_tarski(X66,X67),X68) != k2_tarski(X66,X67) )
      & ( r2_hidden(X66,X68)
        | r2_hidden(X67,X68)
        | k4_xboole_0(k2_tarski(X66,X67),X68) = k2_tarski(X66,X67) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

cnf(c_0_102,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)),k4_xboole_0(k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1),k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1))) = k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))
    | r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_97,c_0_67])).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_96]),c_0_67]),c_0_96]),c_0_67]),c_0_67]),c_0_95]),c_0_46]),c_0_99]),c_0_96]),c_0_67])).

fof(c_0_104,plain,(
    ! [X56,X57] :
      ( ( k4_xboole_0(k1_tarski(X56),X57) != k1_tarski(X56)
        | ~ r2_hidden(X56,X57) )
      & ( r2_hidden(X56,X57)
        | k4_xboole_0(k1_tarski(X56),X57) = k1_tarski(X56) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

fof(c_0_105,plain,(
    ! [X58,X59,X60,X61] :
      ( ( r2_hidden(X58,X60)
        | ~ r2_hidden(k4_tarski(X58,X59),k2_zfmisc_1(X60,X61)) )
      & ( r2_hidden(X59,X61)
        | ~ r2_hidden(k4_tarski(X58,X59),k2_zfmisc_1(X60,X61)) )
      & ( ~ r2_hidden(X58,X60)
        | ~ r2_hidden(X59,X61)
        | r2_hidden(k4_tarski(X58,X59),k2_zfmisc_1(X60,X61)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_106,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4)))
    | X1 != X2
    | X3 != X4 ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_107,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_108,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_109,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | k4_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_110,negated_conjecture,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1))) = k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))
    | r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_80]),c_0_95]),c_0_46])).

cnf(c_0_111,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[c_0_99,c_0_103])).

cnf(c_0_112,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),X3))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_40])).

cnf(c_0_113,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_114,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_115,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_106])])).

cnf(c_0_116,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_117,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_107])).

cnf(c_0_118,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0) = k1_xboole_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_84]),c_0_85])).

cnf(c_0_119,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)
    | r2_hidden(X3,X2)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_84]),c_0_84]),c_0_85]),c_0_85])).

cnf(c_0_120,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X1,X3),X2) != k2_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_121,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0))) = k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)
    | r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111]),c_0_111])).

cnf(c_0_122,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),X2))) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_123,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_124,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_125,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)),k4_xboole_0(k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1),k4_xboole_0(k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1),k1_xboole_0))) = k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_118]),c_0_46])).

cnf(c_0_126,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_127,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)
    | r2_hidden(X1,k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))
    | r2_hidden(X2,k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_119])).

cnf(c_0_128,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_84]),c_0_84]),c_0_85]),c_0_85])).

cnf(c_0_129,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,esk5_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_73]),c_0_95]),c_0_67])).

cnf(c_0_130,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_116,c_0_40])).

cnf(c_0_131,plain,
    ( r2_hidden(X1,k4_xboole_0(k1_tarski(X1),X2))
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_122,c_0_113])).

cnf(c_0_132,plain,
    ( r2_hidden(esk1_2(k1_tarski(X1),k1_tarski(X1)),k1_tarski(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_54]),c_0_124])).

cnf(c_0_133,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)),k4_xboole_0(k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1),k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1))) = k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_125,c_0_67])).

cnf(c_0_134,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0) != k1_xboole_0
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_84]),c_0_85])).

cnf(c_0_135,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3) = k1_xboole_0
    | r2_hidden(X2,k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))
    | r2_hidden(X1,k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_127,c_0_95])).

cnf(c_0_136,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k4_xboole_0(X1,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_130])).

cnf(c_0_137,plain,
    ( r2_hidden(X1,k4_xboole_0(k1_tarski(X1),X2))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_138,negated_conjecture,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1))) = k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_80]),c_0_95]),c_0_46])).

cnf(c_0_139,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_130]),c_0_130])).

cnf(c_0_140,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_141,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0))) = k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_138,c_0_111]),c_0_111])).

cnf(c_0_142,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_140])])).

cnf(c_0_143,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_144,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0))) = k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1) ),
    inference(sr,[status(thm)],[c_0_141,c_0_142])).

cnf(c_0_145,plain,
    ( k4_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),X2) != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_143,c_0_84]),c_0_84]),c_0_85]),c_0_85])).

cnf(c_0_146,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,esk5_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_73]),c_0_95]),c_0_67])).

cnf(c_0_147,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k4_xboole_0(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_145,c_0_146])).

cnf(c_0_148,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_137]),c_0_142]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:43:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 4.93/5.09  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 4.93/5.09  # and selection function SelectNegativeLiterals.
% 4.93/5.09  #
% 4.93/5.09  # Preprocessing time       : 0.029 s
% 4.93/5.09  # Presaturation interreduction done
% 4.93/5.09  
% 4.93/5.09  # Proof found!
% 4.93/5.09  # SZS status Theorem
% 4.93/5.09  # SZS output start CNFRefutation
% 4.93/5.09  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.93/5.09  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.93/5.09  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.93/5.09  fof(l36_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 4.93/5.09  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.93/5.09  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.93/5.09  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.93/5.09  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.93/5.09  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 4.93/5.09  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.93/5.09  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.93/5.09  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.93/5.09  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.93/5.09  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.93/5.09  fof(t73_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 4.93/5.09  fof(t92_enumset1, axiom, ![X1, X2]:k5_enumset1(X1,X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_enumset1)).
% 4.93/5.09  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 4.93/5.09  fof(t93_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 4.93/5.09  fof(t34_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))<=>(X1=X3&X2=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 4.93/5.09  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 4.93/5.09  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 4.93/5.09  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.93/5.09  fof(c_0_22, plain, ![X45, X46]:k2_xboole_0(X45,X46)=k5_xboole_0(k5_xboole_0(X45,X46),k3_xboole_0(X45,X46)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 4.93/5.09  fof(c_0_23, plain, ![X36, X37]:k4_xboole_0(X36,k4_xboole_0(X36,X37))=k3_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 4.93/5.09  fof(c_0_24, plain, ![X38, X39]:k2_xboole_0(k3_xboole_0(X38,X39),k4_xboole_0(X38,X39))=X38, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 4.93/5.09  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.93/5.09  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.93/5.09  fof(c_0_27, plain, ![X24, X25, X26]:k4_xboole_0(X24,k3_xboole_0(X25,X26))=k2_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,X26)), inference(variable_rename,[status(thm)],[l36_xboole_1])).
% 4.93/5.09  fof(c_0_28, plain, ![X18, X19, X21, X22, X23]:((r1_xboole_0(X18,X19)|r2_hidden(esk2_2(X18,X19),k3_xboole_0(X18,X19)))&(~r2_hidden(X23,k3_xboole_0(X21,X22))|~r1_xboole_0(X21,X22))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 4.93/5.09  fof(c_0_29, plain, ![X10, X11]:(~r1_xboole_0(X10,X11)|r1_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 4.93/5.09  fof(c_0_30, plain, ![X41, X42]:r1_xboole_0(k4_xboole_0(X41,X42),X42), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 4.93/5.09  fof(c_0_31, plain, ![X34, X35]:k4_xboole_0(X34,k3_xboole_0(X34,X35))=k4_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 4.93/5.09  fof(c_0_32, plain, ![X40]:((r1_xboole_0(X40,X40)|X40!=k1_xboole_0)&(X40=k1_xboole_0|~r1_xboole_0(X40,X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 4.93/5.09  fof(c_0_33, plain, ![X12, X13, X15, X16, X17]:(((r2_hidden(esk1_2(X12,X13),X12)|r1_xboole_0(X12,X13))&(r2_hidden(esk1_2(X12,X13),X13)|r1_xboole_0(X12,X13)))&(~r2_hidden(X17,X15)|~r2_hidden(X17,X16)|~r1_xboole_0(X15,X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 4.93/5.09  cnf(c_0_34, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.93/5.09  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 4.93/5.09  fof(c_0_36, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k5_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 4.93/5.09  cnf(c_0_37, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 4.93/5.09  cnf(c_0_38, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.93/5.09  cnf(c_0_39, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.93/5.09  cnf(c_0_40, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 4.93/5.09  fof(c_0_41, plain, ![X29, X30]:r1_tarski(k3_xboole_0(X29,X30),X29), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 4.93/5.09  cnf(c_0_42, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 4.93/5.09  cnf(c_0_43, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.93/5.09  cnf(c_0_44, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.93/5.09  cnf(c_0_45, plain, (k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_26]), c_0_35])).
% 4.93/5.09  cnf(c_0_46, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 4.93/5.09  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_26]), c_0_35])).
% 4.93/5.09  cnf(c_0_48, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_38, c_0_26])).
% 4.93/5.09  cnf(c_0_49, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 4.93/5.09  fof(c_0_50, plain, ![X31, X32, X33]:k4_xboole_0(k4_xboole_0(X31,X32),X33)=k4_xboole_0(X31,k2_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 4.93/5.09  fof(c_0_51, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k2_xboole_0(X27,X28)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 4.93/5.09  cnf(c_0_52, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.93/5.09  cnf(c_0_53, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_42, c_0_26])).
% 4.93/5.09  cnf(c_0_54, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,X1),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 4.93/5.09  cnf(c_0_55, plain, (k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 4.93/5.09  cnf(c_0_56, plain, (k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,X2))))=k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_47, c_0_46])).
% 4.93/5.09  cnf(c_0_57, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 4.93/5.09  cnf(c_0_58, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 4.93/5.09  cnf(c_0_59, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 4.93/5.09  cnf(c_0_60, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_52, c_0_26])).
% 4.93/5.09  cnf(c_0_61, plain, (k4_xboole_0(X1,k1_xboole_0)=k4_xboole_0(X1,X2)|r2_hidden(esk1_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 4.93/5.09  cnf(c_0_62, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X2)))=X1), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 4.93/5.09  cnf(c_0_63, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_57, c_0_53])).
% 4.93/5.09  cnf(c_0_64, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[c_0_58, c_0_35])).
% 4.93/5.09  cnf(c_0_65, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_59, c_0_35])).
% 4.93/5.09  cnf(c_0_66, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_60, c_0_53])).
% 4.93/5.09  cnf(c_0_67, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 4.93/5.09  cnf(c_0_68, plain, (k4_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k1_xboole_0),k5_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)|r2_hidden(esk1_2(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)),k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_54]), c_0_46])).
% 4.93/5.09  cnf(c_0_69, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_46])).
% 4.93/5.09  cnf(c_0_70, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_67]), c_0_67]), c_0_67])).
% 4.93/5.09  cnf(c_0_71, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)|r2_hidden(esk1_2(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)),k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_68, c_0_67])).
% 4.93/5.09  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_67]), c_0_70]), c_0_46])).
% 4.93/5.09  cnf(c_0_73, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_63])).
% 4.93/5.09  fof(c_0_74, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3)))), inference(assume_negation,[status(cth)],[t73_zfmisc_1])).
% 4.93/5.09  cnf(c_0_75, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_53, c_0_64])).
% 4.93/5.09  cnf(c_0_76, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_62, c_0_73])).
% 4.93/5.09  fof(c_0_77, negated_conjecture, ((k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0|(~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)))&((r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0)&(r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_74])])])])).
% 4.93/5.09  fof(c_0_78, plain, ![X54, X55]:k5_enumset1(X54,X54,X54,X54,X54,X54,X55)=k2_tarski(X54,X55), inference(variable_rename,[status(thm)],[t92_enumset1])).
% 4.93/5.09  fof(c_0_79, plain, ![X47, X48, X49, X50, X51, X52, X53]:k6_enumset1(X47,X47,X48,X49,X50,X51,X52,X53)=k5_enumset1(X47,X48,X49,X50,X51,X52,X53), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 4.93/5.09  cnf(c_0_80, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 4.93/5.09  cnf(c_0_81, plain, (k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0)))=k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|r2_hidden(esk1_2(k4_xboole_0(X1,X3),k4_xboole_0(X1,X3)),k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_54]), c_0_46])).
% 4.93/5.09  cnf(c_0_82, plain, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),X2))), inference(spm,[status(thm)],[c_0_57, c_0_75])).
% 4.93/5.09  cnf(c_0_83, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_77])).
% 4.93/5.09  cnf(c_0_84, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 4.93/5.09  cnf(c_0_85, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 4.93/5.09  fof(c_0_86, plain, ![X43, X44]:k2_xboole_0(X43,X44)=k2_xboole_0(k5_xboole_0(X43,X44),k3_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[t93_xboole_1])).
% 4.93/5.09  cnf(c_0_87, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_66, c_0_64])).
% 4.93/5.09  cnf(c_0_88, plain, (r1_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_40, c_0_80])).
% 4.93/5.09  cnf(c_0_89, plain, (k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))=k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|r2_hidden(esk1_2(k4_xboole_0(X1,X3),k4_xboole_0(X1,X3)),k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[c_0_81, c_0_67])).
% 4.93/5.09  cnf(c_0_90, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)))=k4_xboole_0(k1_xboole_0,X2)|r2_hidden(esk1_2(k4_xboole_0(X1,X3),k4_xboole_0(X1,X3)),k4_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_75, c_0_54])).
% 4.93/5.09  cnf(c_0_91, plain, (~r2_hidden(X1,k4_xboole_0(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_82, c_0_67])).
% 4.93/5.09  cnf(c_0_92, negated_conjecture, (k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)=k1_xboole_0|r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 4.93/5.09  cnf(c_0_93, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 4.93/5.09  cnf(c_0_94, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_87]), c_0_46])).
% 4.93/5.09  cnf(c_0_95, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_88])).
% 4.93/5.09  cnf(c_0_96, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_67]), c_0_67]), c_0_67]), c_0_67]), c_0_46]), c_0_72]), c_0_91]), c_0_91])).
% 4.93/5.09  cnf(c_0_97, negated_conjecture, (k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)),k4_xboole_0(k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1),k4_xboole_0(k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1),k1_xboole_0)))=k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))|r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_92]), c_0_46])).
% 4.93/5.09  cnf(c_0_98, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_26]), c_0_35]), c_0_35])).
% 4.93/5.09  cnf(c_0_99, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_46]), c_0_96]), c_0_67])).
% 4.93/5.09  fof(c_0_100, plain, ![X62, X63, X64, X65]:(((X62=X64|~r2_hidden(k4_tarski(X62,X63),k2_zfmisc_1(k1_tarski(X64),k1_tarski(X65))))&(X63=X65|~r2_hidden(k4_tarski(X62,X63),k2_zfmisc_1(k1_tarski(X64),k1_tarski(X65)))))&(X62!=X64|X63!=X65|r2_hidden(k4_tarski(X62,X63),k2_zfmisc_1(k1_tarski(X64),k1_tarski(X65))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).
% 4.93/5.09  fof(c_0_101, plain, ![X66, X67, X68]:(((~r2_hidden(X66,X68)|k4_xboole_0(k2_tarski(X66,X67),X68)!=k2_tarski(X66,X67))&(~r2_hidden(X67,X68)|k4_xboole_0(k2_tarski(X66,X67),X68)!=k2_tarski(X66,X67)))&(r2_hidden(X66,X68)|r2_hidden(X67,X68)|k4_xboole_0(k2_tarski(X66,X67),X68)=k2_tarski(X66,X67))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 4.93/5.09  cnf(c_0_102, negated_conjecture, (k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)),k4_xboole_0(k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1),k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)))=k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))|r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[c_0_97, c_0_67])).
% 4.93/5.09  cnf(c_0_103, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_96]), c_0_67]), c_0_96]), c_0_67]), c_0_67]), c_0_95]), c_0_46]), c_0_99]), c_0_96]), c_0_67])).
% 4.93/5.09  fof(c_0_104, plain, ![X56, X57]:((k4_xboole_0(k1_tarski(X56),X57)!=k1_tarski(X56)|~r2_hidden(X56,X57))&(r2_hidden(X56,X57)|k4_xboole_0(k1_tarski(X56),X57)=k1_tarski(X56))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 4.93/5.09  fof(c_0_105, plain, ![X58, X59, X60, X61]:(((r2_hidden(X58,X60)|~r2_hidden(k4_tarski(X58,X59),k2_zfmisc_1(X60,X61)))&(r2_hidden(X59,X61)|~r2_hidden(k4_tarski(X58,X59),k2_zfmisc_1(X60,X61))))&(~r2_hidden(X58,X60)|~r2_hidden(X59,X61)|r2_hidden(k4_tarski(X58,X59),k2_zfmisc_1(X60,X61)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 4.93/5.09  cnf(c_0_106, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4)))|X1!=X2|X3!=X4), inference(split_conjunct,[status(thm)],[c_0_100])).
% 4.93/5.09  cnf(c_0_107, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 4.93/5.09  cnf(c_0_108, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_77])).
% 4.93/5.09  cnf(c_0_109, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|k4_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 4.93/5.09  cnf(c_0_110, negated_conjecture, (k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)))=k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))|r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_80]), c_0_95]), c_0_46])).
% 4.93/5.09  cnf(c_0_111, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[c_0_99, c_0_103])).
% 4.93/5.09  cnf(c_0_112, plain, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),X3)))), inference(spm,[status(thm)],[c_0_48, c_0_40])).
% 4.93/5.09  cnf(c_0_113, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_104])).
% 4.93/5.09  cnf(c_0_114, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_105])).
% 4.93/5.09  cnf(c_0_115, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_106])])).
% 4.93/5.09  cnf(c_0_116, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 4.93/5.09  cnf(c_0_117, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[c_0_107])).
% 4.93/5.09  cnf(c_0_118, negated_conjecture, (k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)=k1_xboole_0|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_84]), c_0_85])).
% 4.93/5.09  cnf(c_0_119, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)|r2_hidden(X3,X2)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_84]), c_0_84]), c_0_85]), c_0_85])).
% 4.93/5.09  cnf(c_0_120, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X1,X3),X2)!=k2_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 4.93/5.09  cnf(c_0_121, negated_conjecture, (k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))=k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)|r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_111]), c_0_111])).
% 4.93/5.09  cnf(c_0_122, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),X2)))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 4.93/5.09  cnf(c_0_123, plain, (r2_hidden(X1,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 4.93/5.09  cnf(c_0_124, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 4.93/5.09  cnf(c_0_125, negated_conjecture, (k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)),k4_xboole_0(k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1),k4_xboole_0(k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1),k1_xboole_0)))=k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_118]), c_0_46])).
% 4.93/5.09  cnf(c_0_126, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0|~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 4.93/5.09  cnf(c_0_127, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)|r2_hidden(X1,k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))|r2_hidden(X2,k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))), inference(spm,[status(thm)],[c_0_53, c_0_119])).
% 4.93/5.09  cnf(c_0_128, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_84]), c_0_84]), c_0_85]), c_0_85])).
% 4.93/5.09  cnf(c_0_129, negated_conjecture, (k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,esk5_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_73]), c_0_95]), c_0_67])).
% 4.93/5.09  cnf(c_0_130, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_116, c_0_40])).
% 4.93/5.09  cnf(c_0_131, plain, (r2_hidden(X1,k4_xboole_0(k1_tarski(X1),X2))|r2_hidden(X1,X2)|~r2_hidden(X3,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_122, c_0_113])).
% 4.93/5.09  cnf(c_0_132, plain, (r2_hidden(esk1_2(k1_tarski(X1),k1_tarski(X1)),k1_tarski(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_54]), c_0_124])).
% 4.93/5.09  cnf(c_0_133, negated_conjecture, (k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)),k4_xboole_0(k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1),k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)))=k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_125, c_0_67])).
% 4.93/5.09  cnf(c_0_134, negated_conjecture, (k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)!=k1_xboole_0|~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_84]), c_0_85])).
% 4.93/5.09  cnf(c_0_135, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)=k1_xboole_0|r2_hidden(X2,k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))|r2_hidden(X1,k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))), inference(rw,[status(thm)],[c_0_127, c_0_95])).
% 4.93/5.09  cnf(c_0_136, negated_conjecture, (~r2_hidden(esk3_0,k4_xboole_0(X1,esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_130])).
% 4.93/5.09  cnf(c_0_137, plain, (r2_hidden(X1,k4_xboole_0(k1_tarski(X1),X2))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_131, c_0_132])).
% 4.93/5.09  cnf(c_0_138, negated_conjecture, (k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)))=k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133, c_0_80]), c_0_95]), c_0_46])).
% 4.93/5.09  cnf(c_0_139, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_130]), c_0_130])).
% 4.93/5.09  cnf(c_0_140, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_136, c_0_137])).
% 4.93/5.09  cnf(c_0_141, negated_conjecture, (k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))=k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_138, c_0_111]), c_0_111])).
% 4.93/5.09  cnf(c_0_142, negated_conjecture, (~r2_hidden(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_139, c_0_140])])).
% 4.93/5.09  cnf(c_0_143, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k2_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 4.93/5.09  cnf(c_0_144, negated_conjecture, (k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)))=k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),X1)), inference(sr,[status(thm)],[c_0_141, c_0_142])).
% 4.93/5.09  cnf(c_0_145, plain, (k4_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),X2)!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_143, c_0_84]), c_0_84]), c_0_85]), c_0_85])).
% 4.93/5.09  cnf(c_0_146, negated_conjecture, (k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k4_xboole_0(X1,esk5_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_73]), c_0_95]), c_0_67])).
% 4.93/5.09  cnf(c_0_147, negated_conjecture, (~r2_hidden(esk4_0,k4_xboole_0(X1,esk5_0))), inference(spm,[status(thm)],[c_0_145, c_0_146])).
% 4.93/5.09  cnf(c_0_148, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_137]), c_0_142]), ['proof']).
% 4.93/5.09  # SZS output end CNFRefutation
% 4.93/5.09  # Proof object total steps             : 149
% 4.93/5.09  # Proof object clause steps            : 104
% 4.93/5.09  # Proof object formula steps           : 45
% 4.93/5.09  # Proof object conjectures             : 26
% 4.93/5.09  # Proof object clause conjectures      : 23
% 4.93/5.09  # Proof object formula conjectures     : 3
% 4.93/5.09  # Proof object initial clauses used    : 28
% 4.93/5.09  # Proof object initial formulas used   : 22
% 4.93/5.09  # Proof object generating inferences   : 44
% 4.93/5.09  # Proof object simplifying inferences  : 98
% 4.93/5.09  # Training examples: 0 positive, 0 negative
% 4.93/5.09  # Parsed axioms                        : 22
% 4.93/5.09  # Removed by relevancy pruning/SinE    : 0
% 4.93/5.09  # Initial clauses                      : 35
% 4.93/5.09  # Removed in clause preprocessing      : 4
% 4.93/5.09  # Initial clauses in saturation        : 31
% 4.93/5.09  # Processed clauses                    : 12057
% 4.93/5.09  # ...of these trivial                  : 227
% 4.93/5.09  # ...subsumed                          : 10572
% 4.93/5.09  # ...remaining for further processing  : 1258
% 4.93/5.09  # Other redundant clauses eliminated   : 412
% 4.93/5.09  # Clauses deleted for lack of memory   : 0
% 4.93/5.09  # Backward-subsumed                    : 87
% 4.93/5.09  # Backward-rewritten                   : 459
% 4.93/5.09  # Generated clauses                    : 362243
% 4.93/5.09  # ...of the previous two non-trivial   : 340832
% 4.93/5.09  # Contextual simplify-reflections      : 15
% 4.93/5.09  # Paramodulations                      : 361809
% 4.93/5.09  # Factorizations                       : 4
% 4.93/5.09  # Equation resolutions                 : 412
% 4.93/5.09  # Propositional unsat checks           : 0
% 4.93/5.09  #    Propositional check models        : 0
% 4.93/5.09  #    Propositional check unsatisfiable : 0
% 4.93/5.09  #    Propositional clauses             : 0
% 4.93/5.09  #    Propositional clauses after purity: 0
% 4.93/5.09  #    Propositional unsat core size     : 0
% 4.93/5.09  #    Propositional preprocessing time  : 0.000
% 4.93/5.09  #    Propositional encoding time       : 0.000
% 4.93/5.09  #    Propositional solver time         : 0.000
% 4.93/5.09  #    Success case prop preproc time    : 0.000
% 4.93/5.09  #    Success case prop encoding time   : 0.000
% 4.93/5.09  #    Success case prop solver time     : 0.000
% 4.93/5.09  # Current number of processed clauses  : 660
% 4.93/5.09  #    Positive orientable unit clauses  : 150
% 4.93/5.09  #    Positive unorientable unit clauses: 6
% 4.93/5.09  #    Negative unit clauses             : 99
% 4.93/5.09  #    Non-unit-clauses                  : 405
% 4.93/5.09  # Current number of unprocessed clauses: 324924
% 4.93/5.09  # ...number of literals in the above   : 749224
% 4.93/5.09  # Current number of archived formulas  : 0
% 4.93/5.09  # Current number of archived clauses   : 600
% 4.93/5.09  # Clause-clause subsumption calls (NU) : 77405
% 4.93/5.09  # Rec. Clause-clause subsumption calls : 61011
% 4.93/5.09  # Non-unit clause-clause subsumptions  : 3447
% 4.93/5.09  # Unit Clause-clause subsumption calls : 10353
% 4.93/5.09  # Rewrite failures with RHS unbound    : 0
% 4.93/5.09  # BW rewrite match attempts            : 2980
% 4.93/5.09  # BW rewrite match successes           : 176
% 4.93/5.09  # Condensation attempts                : 0
% 4.93/5.09  # Condensation successes               : 0
% 4.93/5.09  # Termbank termtop insertions          : 16175963
% 4.93/5.11  
% 4.93/5.11  # -------------------------------------------------
% 4.93/5.11  # User time                : 4.583 s
% 4.93/5.11  # System time              : 0.196 s
% 4.93/5.11  # Total time               : 4.779 s
% 4.93/5.11  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
