%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:20 EST 2020

% Result     : Theorem 0.43s
% Output     : CNFRefutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  135 (4129 expanded)
%              Number of clauses        :   80 (1850 expanded)
%              Number of leaves         :   27 (1079 expanded)
%              Depth                    :   15
%              Number of atoms          :  251 (9308 expanded)
%              Number of equality atoms :  129 (3363 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

fof(c_0_28,plain,(
    ! [X74,X75,X76,X77,X78,X79] :
      ( ( ~ r2_hidden(X76,X75)
        | r1_tarski(X76,X74)
        | X75 != k1_zfmisc_1(X74) )
      & ( ~ r1_tarski(X77,X74)
        | r2_hidden(X77,X75)
        | X75 != k1_zfmisc_1(X74) )
      & ( ~ r2_hidden(esk4_2(X78,X79),X79)
        | ~ r1_tarski(esk4_2(X78,X79),X78)
        | X79 = k1_zfmisc_1(X78) )
      & ( r2_hidden(esk4_2(X78,X79),X79)
        | r1_tarski(esk4_2(X78,X79),X78)
        | X79 = k1_zfmisc_1(X78) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_29,plain,(
    ! [X83,X84] :
      ( ( ~ m1_subset_1(X84,X83)
        | r2_hidden(X84,X83)
        | v1_xboole_0(X83) )
      & ( ~ r2_hidden(X84,X83)
        | m1_subset_1(X84,X83)
        | v1_xboole_0(X83) )
      & ( ~ m1_subset_1(X84,X83)
        | v1_xboole_0(X84)
        | ~ v1_xboole_0(X83) )
      & ( ~ v1_xboole_0(X84)
        | m1_subset_1(X84,X83)
        | ~ v1_xboole_0(X83) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_30,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
    & k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0)) != k2_subset_1(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_31,plain,(
    ! [X90] : ~ v1_xboole_0(k1_zfmisc_1(X90)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28] :
      ( ( r2_hidden(X24,X21)
        | ~ r2_hidden(X24,X23)
        | X23 != k4_xboole_0(X21,X22) )
      & ( ~ r2_hidden(X24,X22)
        | ~ r2_hidden(X24,X23)
        | X23 != k4_xboole_0(X21,X22) )
      & ( ~ r2_hidden(X25,X21)
        | r2_hidden(X25,X22)
        | r2_hidden(X25,X23)
        | X23 != k4_xboole_0(X21,X22) )
      & ( ~ r2_hidden(esk2_3(X26,X27,X28),X28)
        | ~ r2_hidden(esk2_3(X26,X27,X28),X26)
        | r2_hidden(esk2_3(X26,X27,X28),X27)
        | X28 = k4_xboole_0(X26,X27) )
      & ( r2_hidden(esk2_3(X26,X27,X28),X26)
        | r2_hidden(esk2_3(X26,X27,X28),X28)
        | X28 = k4_xboole_0(X26,X27) )
      & ( ~ r2_hidden(esk2_3(X26,X27,X28),X27)
        | r2_hidden(esk2_3(X26,X27,X28),X28)
        | X28 = k4_xboole_0(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_37,plain,(
    ! [X32,X33] : k4_xboole_0(X32,X33) = k5_xboole_0(X32,k3_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_38,plain,(
    ! [X37,X38] :
      ( ~ r1_tarski(X37,X38)
      | k3_xboole_0(X37,X38) = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

fof(c_0_41,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_42,plain,(
    ! [X39,X40] : k4_xboole_0(X39,k4_xboole_0(X39,X40)) = k3_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_45,plain,(
    ! [X34,X35,X36] : k5_xboole_0(k3_xboole_0(X34,X35),k3_xboole_0(X36,X35)) = k3_xboole_0(k5_xboole_0(X34,X36),X35) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_51,plain,(
    ! [X30] :
      ( X30 = k1_xboole_0
      | r2_hidden(esk3_1(X30),X30) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk6_0) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

fof(c_0_54,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( r2_hidden(X15,X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X12)
        | ~ r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X17,X18,X19),X19)
        | ~ r2_hidden(esk1_3(X17,X18,X19),X17)
        | ~ r2_hidden(esk1_3(X17,X18,X19),X18)
        | X19 = k3_xboole_0(X17,X18) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X17)
        | r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k3_xboole_0(X17,X18) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X18)
        | r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k3_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_44]),c_0_44])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(X1,esk6_0)) = k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_48])).

cnf(c_0_59,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1)) = k3_xboole_0(k5_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_48])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk6_0))) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_53])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk3_1(X1),k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1)) = k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(esk6_0,k3_xboole_0(X1,esk5_0)) = k3_xboole_0(esk5_0,k5_xboole_0(esk6_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_53]),c_0_48])).

cnf(c_0_65,negated_conjecture,
    ( k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk5_0)) = k5_xboole_0(esk6_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_53])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_60])).

fof(c_0_67,plain,(
    ! [X42,X43,X44] : k5_xboole_0(k5_xboole_0(X42,X43),X44) = k5_xboole_0(X42,k5_xboole_0(X43,X44)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_68,negated_conjecture,
    ( k3_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk6_0)) = k5_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_61]),c_0_53])).

fof(c_0_69,plain,(
    ! [X86,X87] :
      ( ~ m1_subset_1(X87,k1_zfmisc_1(X86))
      | k3_subset_1(X86,X87) = k4_xboole_0(X86,X87) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_70,plain,(
    ! [X81,X82] : k3_tarski(k2_tarski(X81,X82)) = k2_xboole_0(X81,X82) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_71,plain,(
    ! [X47,X48] : k1_enumset1(X47,X47,X48) = k2_tarski(X47,X48) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk3_1(X1),k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_48])).

cnf(c_0_73,negated_conjecture,
    ( k3_xboole_0(esk5_0,k5_xboole_0(esk6_0,esk6_0)) = k5_xboole_0(esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k5_xboole_0(esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_65])).

cnf(c_0_75,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk6_0)) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_61,c_0_68])).

fof(c_0_77,plain,(
    ! [X88,X89] :
      ( ~ m1_subset_1(X89,k1_zfmisc_1(X88))
      | m1_subset_1(k3_subset_1(X88,X89),k1_zfmisc_1(X88)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_78,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_79,plain,(
    ! [X45,X46] : k2_xboole_0(X45,X46) = k5_xboole_0(k5_xboole_0(X45,X46),k3_xboole_0(X45,X46)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_80,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_81,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

fof(c_0_82,plain,(
    ! [X49,X50,X51] : k2_enumset1(X49,X49,X50,X51) = k1_enumset1(X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_83,plain,(
    ! [X52,X53,X54,X55] : k3_enumset1(X52,X52,X53,X54,X55) = k2_enumset1(X52,X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_84,plain,(
    ! [X56,X57,X58,X59,X60] : k4_enumset1(X56,X56,X57,X58,X59,X60) = k3_enumset1(X56,X57,X58,X59,X60) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_85,plain,(
    ! [X61,X62,X63,X64,X65,X66] : k5_enumset1(X61,X61,X62,X63,X64,X65,X66) = k4_enumset1(X61,X62,X63,X64,X65,X66) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_86,plain,(
    ! [X67,X68,X69,X70,X71,X72,X73] : k6_enumset1(X67,X67,X68,X69,X70,X71,X72,X73) = k5_enumset1(X67,X68,X69,X70,X71,X72,X73) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_87,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk3_1(X1),k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_58])).

cnf(c_0_88,negated_conjecture,
    ( k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,esk6_0))) = esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_64]),c_0_63]),c_0_48]),c_0_53]),c_0_73])).

cnf(c_0_89,negated_conjecture,
    ( k5_xboole_0(esk6_0,esk6_0) = k1_xboole_0
    | r2_hidden(esk3_1(k5_xboole_0(esk6_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_57])).

fof(c_0_90,plain,(
    ! [X41] : k5_xboole_0(X41,k1_xboole_0) = X41 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_91,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_92,negated_conjecture,
    ( k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,X1))) = k5_xboole_0(esk6_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_75])).

fof(c_0_93,plain,(
    ! [X91,X92,X93] :
      ( ~ m1_subset_1(X92,k1_zfmisc_1(X91))
      | ~ m1_subset_1(X93,k1_zfmisc_1(X91))
      | k4_subset_1(X91,X92,X93) = k2_xboole_0(X92,X93) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_94,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_95,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_78,c_0_44])).

cnf(c_0_96,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_97,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_98,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_99,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_100,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_101,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_102,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_103,negated_conjecture,
    ( k5_xboole_0(esk6_0,esk6_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

cnf(c_0_104,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_105,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_106,negated_conjecture,
    ( k3_xboole_0(esk6_0,k5_xboole_0(esk6_0,esk6_0)) = k5_xboole_0(esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_88]),c_0_92])).

fof(c_0_107,plain,(
    ! [X85] : k2_subset_1(X85) = X85 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_108,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_34])).

cnf(c_0_110,negated_conjecture,
    ( k3_subset_1(esk5_0,esk6_0) = k5_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_34]),c_0_53])).

cnf(c_0_111,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97]),c_0_98]),c_0_99]),c_0_100]),c_0_101]),c_0_102])).

cnf(c_0_112,negated_conjecture,
    ( k5_xboole_0(esk5_0,esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_103]),c_0_104])).

cnf(c_0_113,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_114,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_48])).

cnf(c_0_115,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk6_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_103]),c_0_48]),c_0_103])).

cnf(c_0_116,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_48])).

cnf(c_0_117,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0)) != k2_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_118,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_119,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_97]),c_0_98]),c_0_99]),c_0_100]),c_0_101]),c_0_102])).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_121,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_111,c_0_75])).

cnf(c_0_122,negated_conjecture,
    ( k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(X1,k5_xboole_0(esk5_0,esk6_0)))) = k3_xboole_0(k5_xboole_0(esk5_0,X1),k5_xboole_0(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_68]),c_0_75])).

cnf(c_0_123,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3)))))) = k3_xboole_0(k5_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_55]),c_0_75])).

cnf(c_0_124,negated_conjecture,
    ( k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_112]),c_0_113])).

cnf(c_0_125,negated_conjecture,
    ( k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_104]),c_0_63])).

cnf(c_0_126,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,esk6_0)) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_115]),c_0_104]),c_0_48])).

cnf(c_0_127,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_103]),c_0_48]),c_0_103])).

cnf(c_0_128,negated_conjecture,
    ( k5_xboole_0(esk6_0,k5_xboole_0(esk6_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_103]),c_0_113])).

cnf(c_0_129,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0)) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_130,negated_conjecture,
    ( k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(esk5_0,X1),k5_xboole_0(esk5_0,esk6_0))) = k4_subset_1(esk5_0,X1,k5_xboole_0(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_121]),c_0_75]),c_0_122])).

cnf(c_0_131,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk5_0,esk6_0),k5_xboole_0(esk5_0,esk6_0)) = k5_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_122]),c_0_124]),c_0_125]),c_0_48]),c_0_126]),c_0_48]),c_0_127]),c_0_104])).

cnf(c_0_132,negated_conjecture,
    ( k5_xboole_0(esk6_0,k5_xboole_0(X1,esk6_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_128,c_0_105])).

cnf(c_0_133,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k5_xboole_0(esk5_0,esk6_0)) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_129,c_0_110])).

cnf(c_0_134,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_34]),c_0_131]),c_0_132]),c_0_133]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:15:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.43/0.60  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.43/0.60  # and selection function GSelectMinInfpos.
% 0.43/0.60  #
% 0.43/0.60  # Preprocessing time       : 0.028 s
% 0.43/0.60  # Presaturation interreduction done
% 0.43/0.60  
% 0.43/0.60  # Proof found!
% 0.43/0.60  # SZS status Theorem
% 0.43/0.60  # SZS output start CNFRefutation
% 0.43/0.60  fof(t25_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 0.43/0.60  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.43/0.60  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.43/0.60  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.43/0.60  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.43/0.60  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.43/0.60  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.43/0.60  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.43/0.60  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.43/0.60  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 0.43/0.60  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.43/0.60  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.43/0.60  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.43/0.60  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.43/0.60  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.43/0.60  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.43/0.60  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.43/0.60  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.43/0.60  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.43/0.60  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.43/0.60  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.43/0.60  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.43/0.60  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.43/0.60  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.43/0.60  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.43/0.60  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.43/0.60  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.43/0.60  fof(c_0_27, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 0.43/0.60  fof(c_0_28, plain, ![X74, X75, X76, X77, X78, X79]:(((~r2_hidden(X76,X75)|r1_tarski(X76,X74)|X75!=k1_zfmisc_1(X74))&(~r1_tarski(X77,X74)|r2_hidden(X77,X75)|X75!=k1_zfmisc_1(X74)))&((~r2_hidden(esk4_2(X78,X79),X79)|~r1_tarski(esk4_2(X78,X79),X78)|X79=k1_zfmisc_1(X78))&(r2_hidden(esk4_2(X78,X79),X79)|r1_tarski(esk4_2(X78,X79),X78)|X79=k1_zfmisc_1(X78)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.43/0.60  fof(c_0_29, plain, ![X83, X84]:(((~m1_subset_1(X84,X83)|r2_hidden(X84,X83)|v1_xboole_0(X83))&(~r2_hidden(X84,X83)|m1_subset_1(X84,X83)|v1_xboole_0(X83)))&((~m1_subset_1(X84,X83)|v1_xboole_0(X84)|~v1_xboole_0(X83))&(~v1_xboole_0(X84)|m1_subset_1(X84,X83)|~v1_xboole_0(X83)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.43/0.60  fof(c_0_30, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0))!=k2_subset_1(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.43/0.60  fof(c_0_31, plain, ![X90]:~v1_xboole_0(k1_zfmisc_1(X90)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.43/0.60  cnf(c_0_32, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.43/0.60  cnf(c_0_33, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.43/0.60  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.43/0.60  cnf(c_0_35, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.43/0.60  fof(c_0_36, plain, ![X21, X22, X23, X24, X25, X26, X27, X28]:((((r2_hidden(X24,X21)|~r2_hidden(X24,X23)|X23!=k4_xboole_0(X21,X22))&(~r2_hidden(X24,X22)|~r2_hidden(X24,X23)|X23!=k4_xboole_0(X21,X22)))&(~r2_hidden(X25,X21)|r2_hidden(X25,X22)|r2_hidden(X25,X23)|X23!=k4_xboole_0(X21,X22)))&((~r2_hidden(esk2_3(X26,X27,X28),X28)|(~r2_hidden(esk2_3(X26,X27,X28),X26)|r2_hidden(esk2_3(X26,X27,X28),X27))|X28=k4_xboole_0(X26,X27))&((r2_hidden(esk2_3(X26,X27,X28),X26)|r2_hidden(esk2_3(X26,X27,X28),X28)|X28=k4_xboole_0(X26,X27))&(~r2_hidden(esk2_3(X26,X27,X28),X27)|r2_hidden(esk2_3(X26,X27,X28),X28)|X28=k4_xboole_0(X26,X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.43/0.60  fof(c_0_37, plain, ![X32, X33]:k4_xboole_0(X32,X33)=k5_xboole_0(X32,k3_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.43/0.60  fof(c_0_38, plain, ![X37, X38]:(~r1_tarski(X37,X38)|k3_xboole_0(X37,X38)=X37), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.43/0.60  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_32])).
% 0.43/0.60  cnf(c_0_40, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.43/0.60  fof(c_0_41, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.43/0.60  fof(c_0_42, plain, ![X39, X40]:k4_xboole_0(X39,k4_xboole_0(X39,X40))=k3_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.43/0.60  cnf(c_0_43, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.43/0.60  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.43/0.60  fof(c_0_45, plain, ![X34, X35, X36]:k5_xboole_0(k3_xboole_0(X34,X35),k3_xboole_0(X36,X35))=k3_xboole_0(k5_xboole_0(X34,X36),X35), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 0.43/0.60  cnf(c_0_46, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.43/0.60  cnf(c_0_47, negated_conjecture, (r1_tarski(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.43/0.60  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.43/0.60  cnf(c_0_49, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.43/0.60  cnf(c_0_50, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.43/0.60  fof(c_0_51, plain, ![X30]:(X30=k1_xboole_0|r2_hidden(esk3_1(X30),X30)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.43/0.60  cnf(c_0_52, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.43/0.60  cnf(c_0_53, negated_conjecture, (k3_xboole_0(esk5_0,esk6_0)=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.43/0.60  fof(c_0_54, plain, ![X12, X13, X14, X15, X16, X17, X18, X19]:((((r2_hidden(X15,X12)|~r2_hidden(X15,X14)|X14!=k3_xboole_0(X12,X13))&(r2_hidden(X15,X13)|~r2_hidden(X15,X14)|X14!=k3_xboole_0(X12,X13)))&(~r2_hidden(X16,X12)|~r2_hidden(X16,X13)|r2_hidden(X16,X14)|X14!=k3_xboole_0(X12,X13)))&((~r2_hidden(esk1_3(X17,X18,X19),X19)|(~r2_hidden(esk1_3(X17,X18,X19),X17)|~r2_hidden(esk1_3(X17,X18,X19),X18))|X19=k3_xboole_0(X17,X18))&((r2_hidden(esk1_3(X17,X18,X19),X17)|r2_hidden(esk1_3(X17,X18,X19),X19)|X19=k3_xboole_0(X17,X18))&(r2_hidden(esk1_3(X17,X18,X19),X18)|r2_hidden(esk1_3(X17,X18,X19),X19)|X19=k3_xboole_0(X17,X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.43/0.60  cnf(c_0_55, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_44]), c_0_44])).
% 0.43/0.60  cnf(c_0_56, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_50])).
% 0.43/0.60  cnf(c_0_57, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.43/0.60  cnf(c_0_58, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(X1,esk6_0))=k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_48])).
% 0.43/0.60  cnf(c_0_59, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))=k3_xboole_0(k5_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_52, c_0_48])).
% 0.43/0.60  cnf(c_0_60, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.43/0.60  cnf(c_0_61, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk6_0)))=esk6_0), inference(spm,[status(thm)],[c_0_55, c_0_53])).
% 0.43/0.60  cnf(c_0_62, plain, (X1=k1_xboole_0|~r2_hidden(esk3_1(X1),k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.43/0.60  cnf(c_0_63, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(esk6_0,X1))=k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_58, c_0_48])).
% 0.43/0.60  cnf(c_0_64, negated_conjecture, (k5_xboole_0(esk6_0,k3_xboole_0(X1,esk5_0))=k3_xboole_0(esk5_0,k5_xboole_0(esk6_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_53]), c_0_48])).
% 0.43/0.60  cnf(c_0_65, negated_conjecture, (k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk5_0))=k5_xboole_0(esk6_0,esk6_0)), inference(spm,[status(thm)],[c_0_58, c_0_53])).
% 0.43/0.60  cnf(c_0_66, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_60])).
% 0.43/0.60  fof(c_0_67, plain, ![X42, X43, X44]:k5_xboole_0(k5_xboole_0(X42,X43),X44)=k5_xboole_0(X42,k5_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.43/0.60  cnf(c_0_68, negated_conjecture, (k3_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk6_0))=k5_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_61]), c_0_53])).
% 0.43/0.60  fof(c_0_69, plain, ![X86, X87]:(~m1_subset_1(X87,k1_zfmisc_1(X86))|k3_subset_1(X86,X87)=k4_xboole_0(X86,X87)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.43/0.60  fof(c_0_70, plain, ![X81, X82]:k3_tarski(k2_tarski(X81,X82))=k2_xboole_0(X81,X82), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.43/0.60  fof(c_0_71, plain, ![X47, X48]:k1_enumset1(X47,X47,X48)=k2_tarski(X47,X48), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.43/0.60  cnf(c_0_72, plain, (X1=k1_xboole_0|~r2_hidden(esk3_1(X1),k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_62, c_0_48])).
% 0.43/0.60  cnf(c_0_73, negated_conjecture, (k3_xboole_0(esk5_0,k5_xboole_0(esk6_0,esk6_0))=k5_xboole_0(esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.43/0.60  cnf(c_0_74, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,k5_xboole_0(esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_66, c_0_65])).
% 0.43/0.60  cnf(c_0_75, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.43/0.60  cnf(c_0_76, negated_conjecture, (k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk6_0))=esk6_0), inference(rw,[status(thm)],[c_0_61, c_0_68])).
% 0.43/0.60  fof(c_0_77, plain, ![X88, X89]:(~m1_subset_1(X89,k1_zfmisc_1(X88))|m1_subset_1(k3_subset_1(X88,X89),k1_zfmisc_1(X88))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.43/0.60  cnf(c_0_78, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.43/0.60  fof(c_0_79, plain, ![X45, X46]:k2_xboole_0(X45,X46)=k5_xboole_0(k5_xboole_0(X45,X46),k3_xboole_0(X45,X46)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.43/0.60  cnf(c_0_80, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.43/0.60  cnf(c_0_81, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.43/0.60  fof(c_0_82, plain, ![X49, X50, X51]:k2_enumset1(X49,X49,X50,X51)=k1_enumset1(X49,X50,X51), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.43/0.60  fof(c_0_83, plain, ![X52, X53, X54, X55]:k3_enumset1(X52,X52,X53,X54,X55)=k2_enumset1(X52,X53,X54,X55), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.43/0.60  fof(c_0_84, plain, ![X56, X57, X58, X59, X60]:k4_enumset1(X56,X56,X57,X58,X59,X60)=k3_enumset1(X56,X57,X58,X59,X60), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.43/0.60  fof(c_0_85, plain, ![X61, X62, X63, X64, X65, X66]:k5_enumset1(X61,X61,X62,X63,X64,X65,X66)=k4_enumset1(X61,X62,X63,X64,X65,X66), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.43/0.60  fof(c_0_86, plain, ![X67, X68, X69, X70, X71, X72, X73]:k6_enumset1(X67,X67,X68,X69,X70,X71,X72,X73)=k5_enumset1(X67,X68,X69,X70,X71,X72,X73), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.43/0.60  cnf(c_0_87, negated_conjecture, (X1=k1_xboole_0|~r2_hidden(esk3_1(X1),k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,X1)))), inference(spm,[status(thm)],[c_0_72, c_0_58])).
% 0.43/0.60  cnf(c_0_88, negated_conjecture, (k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,esk6_0)))=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_64]), c_0_63]), c_0_48]), c_0_53]), c_0_73])).
% 0.43/0.60  cnf(c_0_89, negated_conjecture, (k5_xboole_0(esk6_0,esk6_0)=k1_xboole_0|r2_hidden(esk3_1(k5_xboole_0(esk6_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_74, c_0_57])).
% 0.43/0.60  fof(c_0_90, plain, ![X41]:k5_xboole_0(X41,k1_xboole_0)=X41, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.43/0.60  fof(c_0_91, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.43/0.60  cnf(c_0_92, negated_conjecture, (k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,X1)))=k5_xboole_0(esk6_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_75])).
% 0.43/0.60  fof(c_0_93, plain, ![X91, X92, X93]:(~m1_subset_1(X92,k1_zfmisc_1(X91))|~m1_subset_1(X93,k1_zfmisc_1(X91))|k4_subset_1(X91,X92,X93)=k2_xboole_0(X92,X93)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.43/0.60  cnf(c_0_94, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.43/0.60  cnf(c_0_95, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_78, c_0_44])).
% 0.43/0.60  cnf(c_0_96, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.43/0.60  cnf(c_0_97, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_80, c_0_81])).
% 0.43/0.60  cnf(c_0_98, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.43/0.60  cnf(c_0_99, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.43/0.60  cnf(c_0_100, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.43/0.60  cnf(c_0_101, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.43/0.60  cnf(c_0_102, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.43/0.60  cnf(c_0_103, negated_conjecture, (k5_xboole_0(esk6_0,esk6_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])).
% 0.43/0.60  cnf(c_0_104, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.43/0.60  cnf(c_0_105, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.43/0.60  cnf(c_0_106, negated_conjecture, (k3_xboole_0(esk6_0,k5_xboole_0(esk6_0,esk6_0))=k5_xboole_0(esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_88]), c_0_92])).
% 0.43/0.60  fof(c_0_107, plain, ![X85]:k2_subset_1(X85)=X85, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.43/0.60  cnf(c_0_108, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.43/0.60  cnf(c_0_109, negated_conjecture, (m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_94, c_0_34])).
% 0.43/0.60  cnf(c_0_110, negated_conjecture, (k3_subset_1(esk5_0,esk6_0)=k5_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_34]), c_0_53])).
% 0.43/0.60  cnf(c_0_111, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97]), c_0_98]), c_0_99]), c_0_100]), c_0_101]), c_0_102])).
% 0.43/0.60  cnf(c_0_112, negated_conjecture, (k5_xboole_0(esk5_0,esk5_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_103]), c_0_104])).
% 0.43/0.60  cnf(c_0_113, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.43/0.60  cnf(c_0_114, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_55, c_0_48])).
% 0.43/0.60  cnf(c_0_115, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk6_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_103]), c_0_48]), c_0_103])).
% 0.43/0.60  cnf(c_0_116, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_52, c_0_48])).
% 0.43/0.60  cnf(c_0_117, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0))!=k2_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.43/0.60  cnf(c_0_118, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_107])).
% 0.43/0.60  cnf(c_0_119, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_97]), c_0_98]), c_0_99]), c_0_100]), c_0_101]), c_0_102])).
% 0.43/0.60  cnf(c_0_120, negated_conjecture, (m1_subset_1(k5_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))), inference(rw,[status(thm)],[c_0_109, c_0_110])).
% 0.43/0.60  cnf(c_0_121, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_111, c_0_75])).
% 0.43/0.60  cnf(c_0_122, negated_conjecture, (k5_xboole_0(esk5_0,k5_xboole_0(esk6_0,k3_xboole_0(X1,k5_xboole_0(esk5_0,esk6_0))))=k3_xboole_0(k5_xboole_0(esk5_0,X1),k5_xboole_0(esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_68]), c_0_75])).
% 0.43/0.60  cnf(c_0_123, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3))))))=k3_xboole_0(k5_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_55]), c_0_75])).
% 0.43/0.60  cnf(c_0_124, negated_conjecture, (k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_112]), c_0_113])).
% 0.43/0.60  cnf(c_0_125, negated_conjecture, (k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_104]), c_0_63])).
% 0.43/0.60  cnf(c_0_126, negated_conjecture, (k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,esk6_0))=k3_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_115]), c_0_104]), c_0_48])).
% 0.43/0.60  cnf(c_0_127, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk5_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_103]), c_0_48]), c_0_103])).
% 0.43/0.60  cnf(c_0_128, negated_conjecture, (k5_xboole_0(esk6_0,k5_xboole_0(esk6_0,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_103]), c_0_113])).
% 0.43/0.60  cnf(c_0_129, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0))!=esk5_0), inference(rw,[status(thm)],[c_0_117, c_0_118])).
% 0.43/0.60  cnf(c_0_130, negated_conjecture, (k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(esk5_0,X1),k5_xboole_0(esk5_0,esk6_0)))=k4_subset_1(esk5_0,X1,k5_xboole_0(esk5_0,esk6_0))|~m1_subset_1(X1,k1_zfmisc_1(esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_121]), c_0_75]), c_0_122])).
% 0.43/0.60  cnf(c_0_131, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk5_0,esk6_0),k5_xboole_0(esk5_0,esk6_0))=k5_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_122]), c_0_124]), c_0_125]), c_0_48]), c_0_126]), c_0_48]), c_0_127]), c_0_104])).
% 0.43/0.60  cnf(c_0_132, negated_conjecture, (k5_xboole_0(esk6_0,k5_xboole_0(X1,esk6_0))=X1), inference(spm,[status(thm)],[c_0_128, c_0_105])).
% 0.43/0.60  cnf(c_0_133, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k5_xboole_0(esk5_0,esk6_0))!=esk5_0), inference(rw,[status(thm)],[c_0_129, c_0_110])).
% 0.43/0.60  cnf(c_0_134, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_34]), c_0_131]), c_0_132]), c_0_133]), ['proof']).
% 0.43/0.60  # SZS output end CNFRefutation
% 0.43/0.60  # Proof object total steps             : 135
% 0.43/0.60  # Proof object clause steps            : 80
% 0.43/0.60  # Proof object formula steps           : 55
% 0.43/0.60  # Proof object conjectures             : 40
% 0.43/0.60  # Proof object clause conjectures      : 37
% 0.43/0.60  # Proof object formula conjectures     : 3
% 0.43/0.60  # Proof object initial clauses used    : 28
% 0.43/0.60  # Proof object initial formulas used   : 27
% 0.43/0.60  # Proof object generating inferences   : 36
% 0.43/0.60  # Proof object simplifying inferences  : 67
% 0.43/0.60  # Training examples: 0 positive, 0 negative
% 0.43/0.60  # Parsed axioms                        : 27
% 0.43/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.43/0.60  # Initial clauses                      : 44
% 0.43/0.60  # Removed in clause preprocessing      : 9
% 0.43/0.60  # Initial clauses in saturation        : 35
% 0.43/0.60  # Processed clauses                    : 1964
% 0.43/0.60  # ...of these trivial                  : 87
% 0.43/0.60  # ...subsumed                          : 1333
% 0.43/0.60  # ...remaining for further processing  : 544
% 0.43/0.60  # Other redundant clauses eliminated   : 8
% 0.43/0.60  # Clauses deleted for lack of memory   : 0
% 0.43/0.60  # Backward-subsumed                    : 3
% 0.43/0.60  # Backward-rewritten                   : 57
% 0.43/0.60  # Generated clauses                    : 14836
% 0.43/0.60  # ...of the previous two non-trivial   : 14301
% 0.43/0.60  # Contextual simplify-reflections      : 1
% 0.43/0.60  # Paramodulations                      : 14750
% 0.43/0.60  # Factorizations                       : 78
% 0.43/0.60  # Equation resolutions                 : 8
% 0.43/0.60  # Propositional unsat checks           : 0
% 0.43/0.60  #    Propositional check models        : 0
% 0.43/0.60  #    Propositional check unsatisfiable : 0
% 0.43/0.60  #    Propositional clauses             : 0
% 0.43/0.60  #    Propositional clauses after purity: 0
% 0.43/0.60  #    Propositional unsat core size     : 0
% 0.43/0.60  #    Propositional preprocessing time  : 0.000
% 0.43/0.60  #    Propositional encoding time       : 0.000
% 0.43/0.60  #    Propositional solver time         : 0.000
% 0.43/0.60  #    Success case prop preproc time    : 0.000
% 0.43/0.60  #    Success case prop encoding time   : 0.000
% 0.43/0.60  #    Success case prop solver time     : 0.000
% 0.43/0.60  # Current number of processed clauses  : 441
% 0.43/0.60  #    Positive orientable unit clauses  : 89
% 0.43/0.60  #    Positive unorientable unit clauses: 10
% 0.43/0.60  #    Negative unit clauses             : 82
% 0.43/0.60  #    Non-unit-clauses                  : 260
% 0.43/0.60  # Current number of unprocessed clauses: 12299
% 0.43/0.60  # ...number of literals in the above   : 35039
% 0.43/0.60  # Current number of archived formulas  : 0
% 0.43/0.60  # Current number of archived clauses   : 104
% 0.43/0.60  # Clause-clause subsumption calls (NU) : 11272
% 0.43/0.60  # Rec. Clause-clause subsumption calls : 7570
% 0.43/0.60  # Non-unit clause-clause subsumptions  : 687
% 0.43/0.60  # Unit Clause-clause subsumption calls : 1303
% 0.43/0.60  # Rewrite failures with RHS unbound    : 0
% 0.43/0.60  # BW rewrite match attempts            : 247
% 0.43/0.60  # BW rewrite match successes           : 118
% 0.43/0.60  # Condensation attempts                : 0
% 0.43/0.60  # Condensation successes               : 0
% 0.43/0.60  # Termbank termtop insertions          : 252852
% 0.45/0.61  
% 0.45/0.61  # -------------------------------------------------
% 0.45/0.61  # User time                : 0.253 s
% 0.45/0.61  # System time              : 0.010 s
% 0.45/0.61  # Total time               : 0.263 s
% 0.45/0.61  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
