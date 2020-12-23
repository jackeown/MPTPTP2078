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
% DateTime   : Thu Dec  3 10:45:37 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  156 (278468 expanded)
%              Number of clauses        :  119 (131821 expanded)
%              Number of leaves         :   18 (72236 expanded)
%              Depth                    :   46
%              Number of atoms          :  277 (485524 expanded)
%              Number of equality atoms :   71 (189772 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

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

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

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

fof(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(esk3_0,esk4_0)
      | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) )
    & ( r1_tarski(esk3_0,esk4_0)
      | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_22,plain,(
    ! [X44] : ~ v1_xboole_0(k1_zfmisc_1(X44)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_tarski(X15,X16)
      | r1_tarski(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

fof(c_0_30,plain,(
    ! [X21,X22] : r1_tarski(k4_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_31,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_32,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_tarski(k4_xboole_0(X26,X27),X28)
      | r1_tarski(X26,k2_xboole_0(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_38,plain,(
    ! [X17] : r1_tarski(k1_xboole_0,X17) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X29,X30] : k4_xboole_0(X29,k4_xboole_0(X29,X30)) = k3_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_45,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,k2_xboole_0(X24,X25))
      | r1_tarski(k4_xboole_0(X23,X24),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_48,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_54,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_41])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_36]),c_0_36])).

cnf(c_0_57,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_59])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_61])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(esk4_0,k1_xboole_0) = k3_xboole_0(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_69,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)) = k3_xboole_0(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_67]),c_0_62]),c_0_66])).

fof(c_0_70,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k2_xboole_0(X12,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_68]),c_0_26])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(k3_xboole_0(esk2_0,esk4_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_69]),c_0_64]),c_0_43])])).

cnf(c_0_73,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(k3_xboole_0(esk2_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_78,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_56])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_75])).

fof(c_0_80,plain,(
    ! [X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | k3_subset_1(X42,X43) = k4_xboole_0(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(esk4_0,k3_xboole_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_59])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_41])).

cnf(c_0_84,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_81]),c_0_82])])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_83])).

cnf(c_0_87,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_84,c_0_36])).

cnf(c_0_88,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_85]),c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( k5_xboole_0(esk4_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_64,c_0_85])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_53])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_43])).

cnf(c_0_93,negated_conjecture,
    ( k1_xboole_0 = k3_subset_1(esk4_0,esk4_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

cnf(c_0_94,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_90])).

fof(c_0_96,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | r1_tarski(k4_xboole_0(X20,X19),k4_xboole_0(X20,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_91]),c_0_59])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(esk4_0))
    | ~ r1_tarski(X1,k3_subset_1(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_26])).

cnf(c_0_100,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_56])).

cnf(c_0_102,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk4_0) = k3_subset_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_85]),c_0_25])])).

cnf(c_0_103,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_subset_1(esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_77])])).

cnf(c_0_105,plain,
    ( r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X1)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_36]),c_0_36])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_107,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X2))) = k3_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_87])).

cnf(c_0_108,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0)) = k3_subset_1(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_85]),c_0_85]),c_0_102]),c_0_102])).

cnf(c_0_109,negated_conjecture,
    ( k5_xboole_0(esk3_0,k1_xboole_0) = k3_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_103]),c_0_62])).

cnf(c_0_110,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = k3_subset_1(X1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_62])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk4_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_77])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(esk2_0,esk3_0))),k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))))
    | r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_113,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_85]),c_0_25])])).

cnf(c_0_114,negated_conjecture,
    ( k3_subset_1(esk3_0,k1_xboole_0) = k3_xboole_0(esk2_0,esk3_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( k1_xboole_0 = k3_subset_1(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_111])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),esk4_0)
    | r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_107]),c_0_108]),c_0_113]),c_0_68])])).

cnf(c_0_117,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = k3_subset_1(esk3_0,k3_subset_1(esk4_0,esk4_0))
    | ~ m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_115]),c_0_115])).

fof(c_0_118,plain,(
    ! [X31,X32] : r1_tarski(X31,k2_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk3_0,k3_subset_1(esk4_0,esk4_0)),esk4_0)
    | r1_tarski(esk3_0,esk4_0)
    | ~ m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_120,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_121,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_87])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk3_0,k3_subset_1(esk4_0,esk4_0)),esk4_0)
    | r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_99]),c_0_111])])).

cnf(c_0_123,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_120])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk4_0,k3_subset_1(esk4_0,esk4_0)))
    | ~ m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_53]),c_0_123])).

cnf(c_0_125,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_53])).

cnf(c_0_126,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | ~ m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_111])])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_99]),c_0_111])])).

cnf(c_0_128,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_127])).

cnf(c_0_129,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X2,esk3_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_128])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_129,c_0_41])).

cnf(c_0_131,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_41])).

cnf(c_0_132,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_133,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_53])).

cnf(c_0_134,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_132])).

cnf(c_0_135,negated_conjecture,
    ( X1 = k3_subset_1(esk4_0,esk4_0)
    | ~ r1_tarski(X1,k3_subset_1(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_111])).

cnf(c_0_136,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_137,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)) = k3_subset_1(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_138,plain,
    ( k3_xboole_0(X1,k3_subset_1(esk4_0,esk4_0)) = k3_subset_1(esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_115]),c_0_115])).

cnf(c_0_139,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_subset_1(esk4_0,esk4_0)) = k3_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_109,c_0_115])).

cnf(c_0_140,plain,
    ( r1_tarski(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3))
    | ~ r1_tarski(k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_101])).

cnf(c_0_141,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k3_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_137]),c_0_138]),c_0_139])).

cnf(c_0_142,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_103]),c_0_115]),c_0_138]),c_0_111])])).

cnf(c_0_143,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(k3_xboole_0(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_142,c_0_73])).

cnf(c_0_144,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_143,c_0_77])).

cnf(c_0_145,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_144]),c_0_82])])).

cnf(c_0_146,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_141,c_0_145])).

cnf(c_0_147,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X2,X1))) = k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_101,c_0_59])).

cnf(c_0_148,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk3_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_146])).

cnf(c_0_149,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk3_0)) = k5_xboole_0(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_146]),c_0_59]),c_0_141]),c_0_145])).

cnf(c_0_150,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_151,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_85]),c_0_102])).

cnf(c_0_152,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_148,c_0_149])).

cnf(c_0_153,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk3_0) = k3_subset_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_145]),c_0_68])])).

cnf(c_0_154,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_150,c_0_127])])).

cnf(c_0_155,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_149]),c_0_152]),c_0_145]),c_0_153]),c_0_154]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:30:17 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 1.81/2.05  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.81/2.05  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.81/2.05  #
% 1.81/2.05  # Preprocessing time       : 0.028 s
% 1.81/2.05  # Presaturation interreduction done
% 1.81/2.05  
% 1.81/2.05  # Proof found!
% 1.81/2.05  # SZS status Theorem
% 1.81/2.05  # SZS output start CNFRefutation
% 1.81/2.05  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 1.81/2.05  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.81/2.05  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.81/2.05  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.81/2.05  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.81/2.05  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.81/2.05  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.81/2.05  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.81/2.05  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.81/2.05  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.81/2.05  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.81/2.05  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.81/2.05  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.81/2.05  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.81/2.05  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.81/2.05  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.81/2.05  fof(t34_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 1.81/2.05  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.81/2.05  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 1.81/2.05  fof(c_0_19, plain, ![X33, X34, X35, X36, X37, X38]:(((~r2_hidden(X35,X34)|r1_tarski(X35,X33)|X34!=k1_zfmisc_1(X33))&(~r1_tarski(X36,X33)|r2_hidden(X36,X34)|X34!=k1_zfmisc_1(X33)))&((~r2_hidden(esk1_2(X37,X38),X38)|~r1_tarski(esk1_2(X37,X38),X37)|X38=k1_zfmisc_1(X37))&(r2_hidden(esk1_2(X37,X38),X38)|r1_tarski(esk1_2(X37,X38),X37)|X38=k1_zfmisc_1(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 1.81/2.05  fof(c_0_20, plain, ![X40, X41]:(((~m1_subset_1(X41,X40)|r2_hidden(X41,X40)|v1_xboole_0(X40))&(~r2_hidden(X41,X40)|m1_subset_1(X41,X40)|v1_xboole_0(X40)))&((~m1_subset_1(X41,X40)|v1_xboole_0(X41)|~v1_xboole_0(X40))&(~v1_xboole_0(X41)|m1_subset_1(X41,X40)|~v1_xboole_0(X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 1.81/2.05  fof(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))&(r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 1.81/2.05  fof(c_0_22, plain, ![X44]:~v1_xboole_0(k1_zfmisc_1(X44)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 1.81/2.05  cnf(c_0_23, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.81/2.05  cnf(c_0_24, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.81/2.05  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.81/2.05  cnf(c_0_26, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.81/2.05  fof(c_0_27, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|~r1_tarski(X15,X16)|r1_tarski(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 1.81/2.05  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_23])).
% 1.81/2.05  cnf(c_0_29, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 1.81/2.05  fof(c_0_30, plain, ![X21, X22]:r1_tarski(k4_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 1.81/2.05  fof(c_0_31, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.81/2.05  fof(c_0_32, plain, ![X26, X27, X28]:(~r1_tarski(k4_xboole_0(X26,X27),X28)|r1_tarski(X26,k2_xboole_0(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 1.81/2.05  cnf(c_0_33, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.81/2.05  cnf(c_0_34, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.81/2.05  cnf(c_0_35, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.81/2.05  cnf(c_0_36, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.81/2.05  fof(c_0_37, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.81/2.05  fof(c_0_38, plain, ![X17]:r1_tarski(k1_xboole_0,X17), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.81/2.05  cnf(c_0_39, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.81/2.05  cnf(c_0_40, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.81/2.05  cnf(c_0_41, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 1.81/2.05  cnf(c_0_42, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.81/2.05  cnf(c_0_43, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.81/2.05  fof(c_0_44, plain, ![X29, X30]:k4_xboole_0(X29,k4_xboole_0(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.81/2.05  fof(c_0_45, plain, ![X23, X24, X25]:(~r1_tarski(X23,k2_xboole_0(X24,X25))|r1_tarski(k4_xboole_0(X23,X24),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 1.81/2.05  cnf(c_0_46, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[c_0_39, c_0_36])).
% 1.81/2.05  cnf(c_0_47, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)),esk2_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.81/2.05  fof(c_0_48, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.81/2.05  cnf(c_0_49, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.81/2.05  cnf(c_0_50, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.81/2.05  cnf(c_0_51, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.81/2.05  cnf(c_0_52, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.81/2.05  cnf(c_0_53, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.81/2.05  fof(c_0_54, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.81/2.05  cnf(c_0_55, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_41])).
% 1.81/2.05  cnf(c_0_56, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_36]), c_0_36])).
% 1.81/2.05  cnf(c_0_57, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_51, c_0_36])).
% 1.81/2.05  cnf(c_0_58, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.81/2.05  cnf(c_0_59, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.81/2.05  cnf(c_0_60, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.81/2.05  cnf(c_0_61, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 1.81/2.05  cnf(c_0_62, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_59])).
% 1.81/2.05  cnf(c_0_63, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_56, c_0_59])).
% 1.81/2.05  cnf(c_0_64, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_61])).
% 1.81/2.05  cnf(c_0_65, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_62])).
% 1.81/2.05  cnf(c_0_66, negated_conjecture, (k5_xboole_0(esk4_0,k1_xboole_0)=k3_xboole_0(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_62])).
% 1.81/2.05  cnf(c_0_67, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 1.81/2.05  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.81/2.05  cnf(c_0_69, negated_conjecture, (k3_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0))=k3_xboole_0(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_67]), c_0_62]), c_0_66])).
% 1.81/2.05  fof(c_0_70, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.81/2.05  cnf(c_0_71, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_68]), c_0_26])).
% 1.81/2.05  cnf(c_0_72, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(k3_xboole_0(esk2_0,esk4_0),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_69]), c_0_64]), c_0_43])])).
% 1.81/2.05  cnf(c_0_73, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 1.81/2.05  cnf(c_0_74, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.81/2.05  cnf(c_0_75, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_71])).
% 1.81/2.05  cnf(c_0_76, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(k3_xboole_0(esk2_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 1.81/2.05  cnf(c_0_77, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_74])).
% 1.81/2.05  cnf(c_0_78, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_41, c_0_56])).
% 1.81/2.05  cnf(c_0_79, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_75])).
% 1.81/2.05  fof(c_0_80, plain, ![X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|k3_subset_1(X42,X43)=k4_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 1.81/2.05  cnf(c_0_81, negated_conjecture, (r1_tarski(esk4_0,k3_xboole_0(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 1.81/2.05  cnf(c_0_82, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_78, c_0_59])).
% 1.81/2.05  cnf(c_0_83, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)),esk2_0)), inference(spm,[status(thm)],[c_0_79, c_0_41])).
% 1.81/2.05  cnf(c_0_84, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.81/2.05  cnf(c_0_85, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_81]), c_0_82])])).
% 1.81/2.05  cnf(c_0_86, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_46, c_0_83])).
% 1.81/2.05  cnf(c_0_87, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_84, c_0_36])).
% 1.81/2.05  cnf(c_0_88, negated_conjecture, (k3_xboole_0(esk4_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_85]), c_0_85])).
% 1.81/2.05  cnf(c_0_89, negated_conjecture, (k5_xboole_0(esk4_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_64, c_0_85])).
% 1.81/2.05  cnf(c_0_90, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.81/2.05  cnf(c_0_91, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_86, c_0_53])).
% 1.81/2.05  cnf(c_0_92, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_43])).
% 1.81/2.05  cnf(c_0_93, negated_conjecture, (k1_xboole_0=k3_subset_1(esk4_0,esk4_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])).
% 1.81/2.05  cnf(c_0_94, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.81/2.05  cnf(c_0_95, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_90])).
% 1.81/2.05  fof(c_0_96, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|r1_tarski(k4_xboole_0(X20,X19),k4_xboole_0(X20,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).
% 1.81/2.05  cnf(c_0_97, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_91]), c_0_59])).
% 1.81/2.05  cnf(c_0_98, negated_conjecture, (r1_tarski(X1,X2)|~m1_subset_1(esk4_0,k1_zfmisc_1(esk4_0))|~r1_tarski(X1,k3_subset_1(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 1.81/2.05  cnf(c_0_99, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_26])).
% 1.81/2.05  cnf(c_0_100, plain, (r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 1.81/2.05  cnf(c_0_101, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_56, c_0_56])).
% 1.81/2.05  cnf(c_0_102, negated_conjecture, (k5_xboole_0(esk2_0,esk4_0)=k3_subset_1(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_85]), c_0_25])])).
% 1.81/2.05  cnf(c_0_103, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_97])).
% 1.81/2.05  cnf(c_0_104, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_subset_1(esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_77])])).
% 1.81/2.05  cnf(c_0_105, plain, (r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X1)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_36]), c_0_36])).
% 1.81/2.05  cnf(c_0_106, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.81/2.05  cnf(c_0_107, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X2)))=k3_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_87])).
% 1.81/2.05  cnf(c_0_108, negated_conjecture, (k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0))=k3_subset_1(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_85]), c_0_85]), c_0_102]), c_0_102])).
% 1.81/2.05  cnf(c_0_109, negated_conjecture, (k5_xboole_0(esk3_0,k1_xboole_0)=k3_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_103]), c_0_62])).
% 1.81/2.05  cnf(c_0_110, plain, (k5_xboole_0(X1,k1_xboole_0)=k3_subset_1(X1,k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_87, c_0_62])).
% 1.81/2.05  cnf(c_0_111, negated_conjecture, (r1_tarski(k3_subset_1(esk4_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_104, c_0_77])).
% 1.81/2.05  cnf(c_0_112, negated_conjecture, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(esk2_0,esk3_0))),k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))))|r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 1.81/2.05  cnf(c_0_113, negated_conjecture, (k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_85]), c_0_25])])).
% 1.81/2.05  cnf(c_0_114, negated_conjecture, (k3_subset_1(esk3_0,k1_xboole_0)=k3_xboole_0(esk2_0,esk3_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 1.81/2.05  cnf(c_0_115, negated_conjecture, (k1_xboole_0=k3_subset_1(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_111])).
% 1.81/2.05  cnf(c_0_116, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,esk3_0),esk4_0)|r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_107]), c_0_108]), c_0_113]), c_0_68])])).
% 1.81/2.05  cnf(c_0_117, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=k3_subset_1(esk3_0,k3_subset_1(esk4_0,esk4_0))|~m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_115]), c_0_115])).
% 1.81/2.05  fof(c_0_118, plain, ![X31, X32]:r1_tarski(X31,k2_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 1.81/2.05  cnf(c_0_119, negated_conjecture, (r1_tarski(k3_subset_1(esk3_0,k3_subset_1(esk4_0,esk4_0)),esk4_0)|r1_tarski(esk3_0,esk4_0)|~m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 1.81/2.05  cnf(c_0_120, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_118])).
% 1.81/2.05  cnf(c_0_121, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(k3_subset_1(X1,X2),X3)), inference(spm,[status(thm)],[c_0_46, c_0_87])).
% 1.81/2.05  cnf(c_0_122, negated_conjecture, (r1_tarski(k3_subset_1(esk3_0,k3_subset_1(esk4_0,esk4_0)),esk4_0)|r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_99]), c_0_111])])).
% 1.81/2.05  cnf(c_0_123, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_120])).
% 1.81/2.05  cnf(c_0_124, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk4_0,k3_subset_1(esk4_0,esk4_0)))|~m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_53]), c_0_123])).
% 1.81/2.05  cnf(c_0_125, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_73, c_0_53])).
% 1.81/2.05  cnf(c_0_126, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|~m1_subset_1(k3_subset_1(esk4_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_111])])).
% 1.81/2.05  cnf(c_0_127, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_99]), c_0_111])])).
% 1.81/2.05  cnf(c_0_128, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_127])).
% 1.81/2.05  cnf(c_0_129, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X2,esk3_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_128])).
% 1.81/2.05  cnf(c_0_130, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_129, c_0_41])).
% 1.81/2.05  cnf(c_0_131, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))))), inference(spm,[status(thm)],[c_0_105, c_0_41])).
% 1.81/2.05  cnf(c_0_132, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)),esk4_0)), inference(spm,[status(thm)],[c_0_130, c_0_131])).
% 1.81/2.05  cnf(c_0_133, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_57, c_0_53])).
% 1.81/2.05  cnf(c_0_134, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_132])).
% 1.81/2.05  cnf(c_0_135, negated_conjecture, (X1=k3_subset_1(esk4_0,esk4_0)|~r1_tarski(X1,k3_subset_1(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_111])).
% 1.81/2.05  cnf(c_0_136, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)),X1)), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 1.81/2.05  cnf(c_0_137, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))=k3_subset_1(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 1.81/2.05  cnf(c_0_138, plain, (k3_xboole_0(X1,k3_subset_1(esk4_0,esk4_0))=k3_subset_1(esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_115]), c_0_115])).
% 1.81/2.05  cnf(c_0_139, negated_conjecture, (k5_xboole_0(esk3_0,k3_subset_1(esk4_0,esk4_0))=k3_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_109, c_0_115])).
% 1.81/2.05  cnf(c_0_140, plain, (r1_tarski(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3))|~r1_tarski(k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3)), inference(spm,[status(thm)],[c_0_46, c_0_101])).
% 1.81/2.05  cnf(c_0_141, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=k3_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_137]), c_0_138]), c_0_139])).
% 1.81/2.05  cnf(c_0_142, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_103]), c_0_115]), c_0_138]), c_0_111])])).
% 1.81/2.05  cnf(c_0_143, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(k3_xboole_0(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_142, c_0_73])).
% 1.81/2.05  cnf(c_0_144, negated_conjecture, (r1_tarski(esk3_0,k3_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_143, c_0_77])).
% 1.81/2.05  cnf(c_0_145, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_144]), c_0_82])])).
% 1.81/2.05  cnf(c_0_146, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk3_0), inference(rw,[status(thm)],[c_0_141, c_0_145])).
% 1.81/2.05  cnf(c_0_147, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X2,X1)))=k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_101, c_0_59])).
% 1.81/2.05  cnf(c_0_148, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk3_0)))=esk3_0), inference(spm,[status(thm)],[c_0_63, c_0_146])).
% 1.81/2.05  cnf(c_0_149, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk3_0))=k5_xboole_0(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_146]), c_0_59]), c_0_141]), c_0_145])).
% 1.81/2.05  cnf(c_0_150, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.81/2.05  cnf(c_0_151, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_85]), c_0_102])).
% 1.81/2.05  cnf(c_0_152, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_148, c_0_149])).
% 1.81/2.05  cnf(c_0_153, negated_conjecture, (k5_xboole_0(esk2_0,esk3_0)=k3_subset_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_145]), c_0_68])])).
% 1.81/2.05  cnf(c_0_154, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_150, c_0_127])])).
% 1.81/2.05  cnf(c_0_155, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_149]), c_0_152]), c_0_145]), c_0_153]), c_0_154]), ['proof']).
% 1.81/2.05  # SZS output end CNFRefutation
% 1.81/2.05  # Proof object total steps             : 156
% 1.81/2.05  # Proof object clause steps            : 119
% 1.81/2.05  # Proof object formula steps           : 37
% 1.81/2.05  # Proof object conjectures             : 72
% 1.81/2.05  # Proof object clause conjectures      : 69
% 1.81/2.05  # Proof object formula conjectures     : 3
% 1.81/2.05  # Proof object initial clauses used    : 24
% 1.81/2.05  # Proof object initial formulas used   : 18
% 1.81/2.05  # Proof object generating inferences   : 78
% 1.81/2.05  # Proof object simplifying inferences  : 79
% 1.81/2.05  # Training examples: 0 positive, 0 negative
% 1.81/2.05  # Parsed axioms                        : 18
% 1.81/2.05  # Removed by relevancy pruning/SinE    : 0
% 1.81/2.05  # Initial clauses                      : 29
% 1.81/2.05  # Removed in clause preprocessing      : 1
% 1.81/2.05  # Initial clauses in saturation        : 28
% 1.81/2.05  # Processed clauses                    : 16033
% 1.81/2.05  # ...of these trivial                  : 509
% 1.81/2.05  # ...subsumed                          : 13207
% 1.81/2.05  # ...remaining for further processing  : 2317
% 1.81/2.05  # Other redundant clauses eliminated   : 4
% 1.81/2.05  # Clauses deleted for lack of memory   : 0
% 1.81/2.05  # Backward-subsumed                    : 217
% 1.81/2.05  # Backward-rewritten                   : 321
% 1.81/2.05  # Generated clauses                    : 154158
% 1.81/2.05  # ...of the previous two non-trivial   : 125715
% 1.81/2.05  # Contextual simplify-reflections      : 11
% 1.81/2.05  # Paramodulations                      : 154028
% 1.81/2.05  # Factorizations                       : 126
% 1.81/2.05  # Equation resolutions                 : 4
% 1.81/2.05  # Propositional unsat checks           : 0
% 1.81/2.05  #    Propositional check models        : 0
% 1.81/2.05  #    Propositional check unsatisfiable : 0
% 1.81/2.05  #    Propositional clauses             : 0
% 1.81/2.05  #    Propositional clauses after purity: 0
% 1.81/2.05  #    Propositional unsat core size     : 0
% 1.81/2.05  #    Propositional preprocessing time  : 0.000
% 1.81/2.05  #    Propositional encoding time       : 0.000
% 1.81/2.05  #    Propositional solver time         : 0.000
% 1.81/2.05  #    Success case prop preproc time    : 0.000
% 1.81/2.05  #    Success case prop encoding time   : 0.000
% 1.81/2.05  #    Success case prop solver time     : 0.000
% 1.81/2.05  # Current number of processed clauses  : 1748
% 1.81/2.05  #    Positive orientable unit clauses  : 435
% 1.81/2.05  #    Positive unorientable unit clauses: 2
% 1.81/2.05  #    Negative unit clauses             : 125
% 1.81/2.05  #    Non-unit-clauses                  : 1186
% 1.81/2.05  # Current number of unprocessed clauses: 107616
% 1.81/2.05  # ...number of literals in the above   : 344122
% 1.81/2.05  # Current number of archived formulas  : 0
% 1.81/2.05  # Current number of archived clauses   : 566
% 1.81/2.05  # Clause-clause subsumption calls (NU) : 257542
% 1.81/2.05  # Rec. Clause-clause subsumption calls : 176392
% 1.81/2.05  # Non-unit clause-clause subsumptions  : 7144
% 1.81/2.05  # Unit Clause-clause subsumption calls : 25930
% 1.81/2.05  # Rewrite failures with RHS unbound    : 0
% 1.81/2.05  # BW rewrite match attempts            : 5593
% 1.81/2.05  # BW rewrite match successes           : 85
% 1.81/2.05  # Condensation attempts                : 0
% 1.81/2.05  # Condensation successes               : 0
% 1.81/2.05  # Termbank termtop insertions          : 2754001
% 1.81/2.06  
% 1.81/2.06  # -------------------------------------------------
% 1.81/2.06  # User time                : 1.644 s
% 1.81/2.06  # System time              : 0.063 s
% 1.81/2.06  # Total time               : 1.706 s
% 1.81/2.06  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
