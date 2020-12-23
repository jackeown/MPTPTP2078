%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:46 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  117 (1170 expanded)
%              Number of clauses        :   78 ( 543 expanded)
%              Number of leaves         :   19 ( 295 expanded)
%              Depth                    :   15
%              Number of atoms          :  212 (2546 expanded)
%              Number of equality atoms :   57 ( 783 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t35_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,k3_subset_1(X1,X3))
           => r1_tarski(X3,k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(c_0_19,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ( ~ r2_hidden(X35,X34)
        | r1_tarski(X35,X33)
        | X34 != k1_zfmisc_1(X33) )
      & ( ~ r1_tarski(X36,X33)
        | r2_hidden(X36,X34)
        | X34 != k1_zfmisc_1(X33) )
      & ( ~ r2_hidden(esk1_2(X37,X38),X38)
        | ~ r1_tarski(esk1_2(X37,X38),X37)
        | X38 = k1_zfmisc_1(X37) )
      & ( r2_hidden(esk1_2(X37,X38),X38)
        | r1_tarski(esk1_2(X37,X38),X37)
        | X38 = k1_zfmisc_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_20,plain,(
    ! [X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | k3_subset_1(X42,X43) = k4_xboole_0(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_21,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,k3_subset_1(X1,X3))
             => r1_tarski(X3,k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t35_subset_1])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X28,X29] : r1_tarski(X28,k2_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_25,plain,(
    ! [X12,X13,X14] :
      ( ( r1_tarski(X12,X13)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) )
      & ( r1_xboole_0(X12,X14)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_26,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))
    & ~ r1_tarski(esk4_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_29,plain,(
    ! [X40,X41] :
      ( ( ~ m1_subset_1(X41,X40)
        | r2_hidden(X41,X40)
        | v1_xboole_0(X40) )
      & ( ~ r2_hidden(X41,X40)
        | m1_subset_1(X41,X40)
        | v1_xboole_0(X40) )
      & ( ~ m1_subset_1(X41,X40)
        | v1_xboole_0(X41)
        | ~ v1_xboole_0(X40) )
      & ( ~ v1_xboole_0(X41)
        | m1_subset_1(X41,X40)
        | ~ v1_xboole_0(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X44] : ~ v1_xboole_0(k1_zfmisc_1(X44)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_33,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_42,plain,(
    ! [X21,X22] : r1_tarski(k4_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_43,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(X30,X31)
      | ~ r1_xboole_0(X30,X32)
      | r1_tarski(X30,k4_xboole_0(X31,X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_45,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)) = k3_subset_1(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_46,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,k2_xboole_0(X24,X25))
      | r1_tarski(k4_xboole_0(X23,X24),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_41])).

fof(c_0_50,plain,(
    ! [X20] : r1_tarski(k1_xboole_0,X20) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_51,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(X1,esk4_0)
    | ~ r1_tarski(X1,k3_subset_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_56,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_49])).

fof(c_0_61,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_62,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_63,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_51,c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)) = k3_subset_1(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_52])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[c_0_53,c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_68,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k2_xboole_0(X15,X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_69,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_27])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k2_xboole_0(X2,X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_39])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_60]),c_0_39])).

cnf(c_0_73,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_76,plain,(
    ! [X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(X45))
      | k3_subset_1(X45,k3_subset_1(X45,X46)) = X46 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk4_0)))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_78,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_48])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k3_subset_1(X1,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_72])).

fof(c_0_82,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_83,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_27]),c_0_27])).

cnf(c_0_84,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_64])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_75])).

cnf(c_0_86,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk3_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_49])).

cnf(c_0_88,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_64]),c_0_48])).

cnf(c_0_89,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

fof(c_0_90,plain,(
    ! [X47] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X47)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_91,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_92,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_85]),c_0_39])).

cnf(c_0_94,negated_conjecture,
    ( k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_52])).

cnf(c_0_95,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_87]),c_0_88])).

cnf(c_0_96,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_89])).

cnf(c_0_97,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_98,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_99,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_86,c_0_72])).

cnf(c_0_100,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0))) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_93]),c_0_94])).

cnf(c_0_101,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_91])).

cnf(c_0_102,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_95]),c_0_81]),c_0_96])).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_97]),c_0_98])).

cnf(c_0_104,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_99,c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0)) = k3_subset_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_100]),c_0_65])).

cnf(c_0_106,negated_conjecture,
    ( r1_xboole_0(X1,esk3_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103]),c_0_104])).

cnf(c_0_107,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_83])).

cnf(c_0_108,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_100,c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_49])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_36]),c_0_39])).

cnf(c_0_111,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_105]),c_0_105]),c_0_108]),c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0)))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk3_0) = k3_subset_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_65,c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_111]),c_0_114]),c_0_115]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:24:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S04DN
% 0.19/0.44  # and selection function SelectNewComplex.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.027 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.44  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.44  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.44  fof(t35_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X3))=>r1_tarski(X3,k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 0.19/0.44  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.44  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.19/0.44  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.44  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.19/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.44  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.44  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.44  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.19/0.44  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.19/0.44  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.44  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.44  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.44  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.19/0.44  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.44  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.44  fof(c_0_19, plain, ![X33, X34, X35, X36, X37, X38]:(((~r2_hidden(X35,X34)|r1_tarski(X35,X33)|X34!=k1_zfmisc_1(X33))&(~r1_tarski(X36,X33)|r2_hidden(X36,X34)|X34!=k1_zfmisc_1(X33)))&((~r2_hidden(esk1_2(X37,X38),X38)|~r1_tarski(esk1_2(X37,X38),X37)|X38=k1_zfmisc_1(X37))&(r2_hidden(esk1_2(X37,X38),X38)|r1_tarski(esk1_2(X37,X38),X37)|X38=k1_zfmisc_1(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.44  fof(c_0_20, plain, ![X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|k3_subset_1(X42,X43)=k4_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.44  fof(c_0_21, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.44  fof(c_0_22, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X3))=>r1_tarski(X3,k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t35_subset_1])).
% 0.19/0.44  cnf(c_0_23, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  fof(c_0_24, plain, ![X28, X29]:r1_tarski(X28,k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.44  fof(c_0_25, plain, ![X12, X13, X14]:((r1_tarski(X12,X13)|~r1_tarski(X12,k4_xboole_0(X13,X14)))&(r1_xboole_0(X12,X14)|~r1_tarski(X12,k4_xboole_0(X13,X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.19/0.44  cnf(c_0_26, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.44  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.44  fof(c_0_28, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&(r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))&~r1_tarski(esk4_0,k3_subset_1(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.19/0.44  fof(c_0_29, plain, ![X40, X41]:(((~m1_subset_1(X41,X40)|r2_hidden(X41,X40)|v1_xboole_0(X40))&(~r2_hidden(X41,X40)|m1_subset_1(X41,X40)|v1_xboole_0(X40)))&((~m1_subset_1(X41,X40)|v1_xboole_0(X41)|~v1_xboole_0(X40))&(~v1_xboole_0(X41)|m1_subset_1(X41,X40)|~v1_xboole_0(X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.44  cnf(c_0_30, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_23])).
% 0.19/0.44  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.44  fof(c_0_32, plain, ![X44]:~v1_xboole_0(k1_zfmisc_1(X44)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.44  fof(c_0_33, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.44  cnf(c_0_34, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.44  cnf(c_0_35, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.44  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_37, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.44  cnf(c_0_38, plain, (r2_hidden(X1,k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.44  cnf(c_0_39, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.44  fof(c_0_40, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.44  cnf(c_0_41, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.44  fof(c_0_42, plain, ![X21, X22]:r1_tarski(k4_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.44  fof(c_0_43, plain, ![X30, X31, X32]:(~r1_tarski(X30,X31)|~r1_xboole_0(X30,X32)|r1_tarski(X30,k4_xboole_0(X31,X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 0.19/0.44  cnf(c_0_44, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_34, c_0_27])).
% 0.19/0.44  cnf(c_0_45, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))=k3_subset_1(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.44  fof(c_0_46, plain, ![X23, X24, X25]:(~r1_tarski(X23,k2_xboole_0(X24,X25))|r1_tarski(k4_xboole_0(X23,X24),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.19/0.44  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.19/0.44  cnf(c_0_48, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.44  cnf(c_0_49, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_41])).
% 0.19/0.44  fof(c_0_50, plain, ![X20]:r1_tarski(k1_xboole_0,X20), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.44  cnf(c_0_51, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.44  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_53, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.44  cnf(c_0_54, negated_conjecture, (r1_xboole_0(X1,esk4_0)|~r1_tarski(X1,k3_subset_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.44  cnf(c_0_55, negated_conjecture, (r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_56, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.44  cnf(c_0_57, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_58, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.44  cnf(c_0_59, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.44  cnf(c_0_60, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_49])).
% 0.19/0.44  fof(c_0_61, plain, ![X26, X27]:k4_xboole_0(X26,k4_xboole_0(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.44  cnf(c_0_62, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.44  cnf(c_0_63, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.44  cnf(c_0_64, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_51, c_0_27])).
% 0.19/0.44  cnf(c_0_65, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))=k3_subset_1(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_35, c_0_52])).
% 0.19/0.44  cnf(c_0_66, plain, (r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(rw,[status(thm)],[c_0_53, c_0_27])).
% 0.19/0.44  cnf(c_0_67, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.44  fof(c_0_68, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k2_xboole_0(X15,X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.44  cnf(c_0_69, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_56, c_0_27])).
% 0.19/0.44  cnf(c_0_70, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_57])).
% 0.19/0.44  cnf(c_0_71, plain, (r2_hidden(X1,k1_zfmisc_1(k2_xboole_0(X2,X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_39])).
% 0.19/0.44  cnf(c_0_72, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_60]), c_0_39])).
% 0.19/0.44  cnf(c_0_73, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.44  cnf(c_0_74, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.44  cnf(c_0_75, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.44  fof(c_0_76, plain, ![X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(X45))|k3_subset_1(X45,k3_subset_1(X45,X46))=X46), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.19/0.44  cnf(c_0_77, negated_conjecture, (r1_tarski(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk4_0)))|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.44  cnf(c_0_78, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.44  cnf(c_0_79, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_69, c_0_48])).
% 0.19/0.44  cnf(c_0_80, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.44  cnf(c_0_81, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k3_subset_1(X1,X1)), inference(spm,[status(thm)],[c_0_35, c_0_72])).
% 0.19/0.44  fof(c_0_82, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.44  cnf(c_0_83, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_27]), c_0_27])).
% 0.19/0.44  cnf(c_0_84, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_64])).
% 0.19/0.44  cnf(c_0_85, negated_conjecture, (r2_hidden(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_30, c_0_75])).
% 0.19/0.44  cnf(c_0_86, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.44  cnf(c_0_87, negated_conjecture, (r1_tarski(esk3_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_77, c_0_49])).
% 0.19/0.44  cnf(c_0_88, plain, (k2_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_64]), c_0_48])).
% 0.19/0.44  cnf(c_0_89, plain, (r1_tarski(k3_subset_1(X1,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.19/0.44  fof(c_0_90, plain, ![X47]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X47)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.44  cnf(c_0_91, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.19/0.44  cnf(c_0_92, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.19/0.44  cnf(c_0_93, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_85]), c_0_39])).
% 0.19/0.44  cnf(c_0_94, negated_conjecture, (k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_86, c_0_52])).
% 0.19/0.44  cnf(c_0_95, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_87]), c_0_88])).
% 0.19/0.44  cnf(c_0_96, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_89])).
% 0.19/0.44  cnf(c_0_97, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.19/0.44  cnf(c_0_98, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.19/0.44  cnf(c_0_99, plain, (k3_subset_1(X1,k3_subset_1(X1,X1))=X1), inference(spm,[status(thm)],[c_0_86, c_0_72])).
% 0.19/0.44  cnf(c_0_100, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0)))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_93]), c_0_94])).
% 0.19/0.44  cnf(c_0_101, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_44, c_0_91])).
% 0.19/0.44  cnf(c_0_102, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_95]), c_0_81]), c_0_96])).
% 0.19/0.44  cnf(c_0_103, plain, (k5_xboole_0(X1,k1_xboole_0)=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_97]), c_0_98])).
% 0.19/0.44  cnf(c_0_104, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_99, c_0_96])).
% 0.19/0.44  cnf(c_0_105, negated_conjecture, (k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0))=k3_subset_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_100]), c_0_65])).
% 0.19/0.44  cnf(c_0_106, negated_conjecture, (r1_xboole_0(X1,esk3_0)|~r1_tarski(X1,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103]), c_0_104])).
% 0.19/0.44  cnf(c_0_107, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_83, c_0_83])).
% 0.19/0.44  cnf(c_0_108, negated_conjecture, (k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_100, c_0_105])).
% 0.19/0.44  cnf(c_0_109, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_106, c_0_49])).
% 0.19/0.44  cnf(c_0_110, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_36]), c_0_39])).
% 0.19/0.44  cnf(c_0_111, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_105]), c_0_105]), c_0_108]), c_0_108])).
% 0.19/0.44  cnf(c_0_112, negated_conjecture, (r1_tarski(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0)))|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_66, c_0_109])).
% 0.19/0.44  cnf(c_0_113, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_70, c_0_110])).
% 0.19/0.44  cnf(c_0_114, negated_conjecture, (k5_xboole_0(esk2_0,esk3_0)=k3_subset_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_65, c_0_111])).
% 0.19/0.44  cnf(c_0_115, negated_conjecture, (~r1_tarski(esk4_0,k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_116, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_111]), c_0_114]), c_0_115]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 117
% 0.19/0.44  # Proof object clause steps            : 78
% 0.19/0.44  # Proof object formula steps           : 39
% 0.19/0.44  # Proof object conjectures             : 30
% 0.19/0.44  # Proof object clause conjectures      : 27
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 25
% 0.19/0.44  # Proof object initial formulas used   : 19
% 0.19/0.44  # Proof object generating inferences   : 41
% 0.19/0.44  # Proof object simplifying inferences  : 34
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 20
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 32
% 0.19/0.44  # Removed in clause preprocessing      : 1
% 0.19/0.44  # Initial clauses in saturation        : 31
% 0.19/0.44  # Processed clauses                    : 1032
% 0.19/0.44  # ...of these trivial                  : 149
% 0.19/0.44  # ...subsumed                          : 360
% 0.19/0.44  # ...remaining for further processing  : 523
% 0.19/0.44  # Other redundant clauses eliminated   : 4
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 7
% 0.19/0.44  # Backward-rewritten                   : 207
% 0.19/0.44  # Generated clauses                    : 5041
% 0.19/0.44  # ...of the previous two non-trivial   : 3556
% 0.19/0.44  # Contextual simplify-reflections      : 0
% 0.19/0.44  # Paramodulations                      : 5037
% 0.19/0.44  # Factorizations                       : 0
% 0.19/0.44  # Equation resolutions                 : 4
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 275
% 0.19/0.44  #    Positive orientable unit clauses  : 162
% 0.19/0.44  #    Positive unorientable unit clauses: 2
% 0.19/0.44  #    Negative unit clauses             : 2
% 0.19/0.44  #    Non-unit-clauses                  : 109
% 0.19/0.44  # Current number of unprocessed clauses: 2294
% 0.19/0.44  # ...number of literals in the above   : 2893
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 245
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 8404
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 6523
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 328
% 0.19/0.44  # Unit Clause-clause subsumption calls : 1075
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 387
% 0.19/0.44  # BW rewrite match successes           : 83
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 57917
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.098 s
% 0.19/0.44  # System time              : 0.004 s
% 0.19/0.44  # Total time               : 0.103 s
% 0.19/0.44  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
