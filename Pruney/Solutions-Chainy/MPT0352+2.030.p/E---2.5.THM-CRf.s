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
% DateTime   : Thu Dec  3 10:45:40 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 174 expanded)
%              Number of clauses        :   41 (  76 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  169 ( 398 expanded)
%              Number of equality atoms :   28 (  88 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_16,plain,(
    ! [X10,X11,X12] :
      ( ( r1_tarski(X10,X11)
        | ~ r1_tarski(X10,k4_xboole_0(X11,X12)) )
      & ( r1_xboole_0(X10,X12)
        | ~ r1_tarski(X10,k4_xboole_0(X11,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_17,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | k3_subset_1(X39,X40) = k4_xboole_0(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_19,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | r1_tarski(k4_xboole_0(X20,X19),k4_xboole_0(X20,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

fof(c_0_20,plain,(
    ! [X35,X36] : k3_tarski(k2_tarski(X35,X36)) = k2_xboole_0(X35,X36) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

cnf(c_0_26,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,k2_xboole_0(X24,X25))
      | ~ r1_xboole_0(X23,X25)
      | r1_tarski(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

cnf(c_0_28,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X21,X22] : k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22)) = X21 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_23])).

fof(c_0_33,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(esk3_0,esk4_0)
      | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) )
    & ( r1_tarski(esk3_0,esk4_0)
      | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_34,plain,
    ( r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X1)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_23]),c_0_23])).

fof(c_0_35,plain,(
    ! [X37,X38] :
      ( ( ~ m1_subset_1(X38,X37)
        | r2_hidden(X38,X37)
        | v1_xboole_0(X37) )
      & ( ~ r2_hidden(X38,X37)
        | m1_subset_1(X38,X37)
        | v1_xboole_0(X37) )
      & ( ~ m1_subset_1(X38,X37)
        | v1_xboole_0(X38)
        | ~ v1_xboole_0(X37) )
      & ( ~ v1_xboole_0(X38)
        | m1_subset_1(X38,X37)
        | ~ v1_xboole_0(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_36,plain,(
    ! [X41] : ~ v1_xboole_0(k1_zfmisc_1(X41)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_40,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_subset_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

fof(c_0_45,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X30,X29)
        | r1_tarski(X30,X28)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r1_tarski(X31,X28)
        | r2_hidden(X31,X29)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r2_hidden(esk1_2(X32,X33),X33)
        | ~ r1_tarski(esk1_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) )
      & ( r2_hidden(esk1_2(X32,X33),X33)
        | r1_tarski(esk1_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_48,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X16,X17)
      | r1_tarski(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_49,plain,(
    ! [X13,X14] : r1_tarski(k3_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_51,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_38]),c_0_23])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_55,plain,
    ( r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_32])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_43]),c_0_47])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_61,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_43]),c_0_56])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | k1_zfmisc_1(esk2_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,k3_subset_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_32])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_56]),c_0_70])])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:21:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.46/0.66  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.46/0.66  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.46/0.66  #
% 0.46/0.66  # Preprocessing time       : 0.039 s
% 0.46/0.66  
% 0.46/0.66  # Proof found!
% 0.46/0.66  # SZS status Theorem
% 0.46/0.66  # SZS output start CNFRefutation
% 0.46/0.66  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.46/0.66  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.46/0.66  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.46/0.66  fof(t34_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 0.46/0.66  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.46/0.66  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.46/0.66  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 0.46/0.66  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.46/0.66  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.46/0.66  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.46/0.66  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.46/0.66  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.46/0.66  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.46/0.66  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.46/0.66  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.46/0.66  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.46/0.66  fof(c_0_16, plain, ![X10, X11, X12]:((r1_tarski(X10,X11)|~r1_tarski(X10,k4_xboole_0(X11,X12)))&(r1_xboole_0(X10,X12)|~r1_tarski(X10,k4_xboole_0(X11,X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.46/0.66  fof(c_0_17, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.46/0.66  fof(c_0_18, plain, ![X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(X39))|k3_subset_1(X39,X40)=k4_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.46/0.66  fof(c_0_19, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|r1_tarski(k4_xboole_0(X20,X19),k4_xboole_0(X20,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).
% 0.46/0.66  fof(c_0_20, plain, ![X35, X36]:k3_tarski(k2_tarski(X35,X36))=k2_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.46/0.66  fof(c_0_21, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.46/0.66  cnf(c_0_22, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.46/0.66  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.46/0.66  cnf(c_0_24, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.66  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 0.46/0.66  cnf(c_0_26, plain, (r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.66  fof(c_0_27, plain, ![X23, X24, X25]:(~r1_tarski(X23,k2_xboole_0(X24,X25))|~r1_xboole_0(X23,X25)|r1_tarski(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 0.46/0.66  cnf(c_0_28, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.46/0.66  cnf(c_0_29, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.46/0.66  fof(c_0_30, plain, ![X21, X22]:k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))=X21, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.46/0.66  cnf(c_0_31, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.46/0.66  cnf(c_0_32, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_24, c_0_23])).
% 0.46/0.66  fof(c_0_33, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))&(r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.46/0.66  cnf(c_0_34, plain, (r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X1)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_23]), c_0_23])).
% 0.46/0.66  fof(c_0_35, plain, ![X37, X38]:(((~m1_subset_1(X38,X37)|r2_hidden(X38,X37)|v1_xboole_0(X37))&(~r2_hidden(X38,X37)|m1_subset_1(X38,X37)|v1_xboole_0(X37)))&((~m1_subset_1(X38,X37)|v1_xboole_0(X38)|~v1_xboole_0(X37))&(~v1_xboole_0(X38)|m1_subset_1(X38,X37)|~v1_xboole_0(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.46/0.66  fof(c_0_36, plain, ![X41]:~v1_xboole_0(k1_zfmisc_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.46/0.66  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.46/0.66  cnf(c_0_38, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.46/0.66  cnf(c_0_39, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.46/0.66  fof(c_0_40, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.46/0.66  cnf(c_0_41, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k3_subset_1(X3,X2))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.46/0.66  cnf(c_0_42, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.46/0.66  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.46/0.66  cnf(c_0_44, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_subset_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_34, c_0_32])).
% 0.46/0.66  fof(c_0_45, plain, ![X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X30,X29)|r1_tarski(X30,X28)|X29!=k1_zfmisc_1(X28))&(~r1_tarski(X31,X28)|r2_hidden(X31,X29)|X29!=k1_zfmisc_1(X28)))&((~r2_hidden(esk1_2(X32,X33),X33)|~r1_tarski(esk1_2(X32,X33),X32)|X33=k1_zfmisc_1(X32))&(r2_hidden(esk1_2(X32,X33),X33)|r1_tarski(esk1_2(X32,X33),X32)|X33=k1_zfmisc_1(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.46/0.66  cnf(c_0_46, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.46/0.66  cnf(c_0_47, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.46/0.66  fof(c_0_48, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_tarski(X16,X17)|r1_tarski(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.46/0.66  fof(c_0_49, plain, ![X13, X14]:r1_tarski(k3_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.46/0.66  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.46/0.66  cnf(c_0_51, plain, (k3_tarski(k1_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_38]), c_0_23])).
% 0.46/0.66  cnf(c_0_52, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.46/0.66  cnf(c_0_53, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.46/0.66  cnf(c_0_54, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.46/0.66  cnf(c_0_55, plain, (r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_44, c_0_32])).
% 0.46/0.66  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.46/0.66  cnf(c_0_57, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.46/0.66  cnf(c_0_58, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_43]), c_0_47])).
% 0.46/0.66  cnf(c_0_59, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.46/0.66  cnf(c_0_60, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.46/0.66  fof(c_0_61, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.46/0.66  cnf(c_0_62, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.46/0.66  cnf(c_0_63, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.46/0.66  cnf(c_0_64, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_43]), c_0_56])])).
% 0.46/0.66  cnf(c_0_65, negated_conjecture, (r1_tarski(esk3_0,X1)|k1_zfmisc_1(esk2_0)!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.46/0.66  cnf(c_0_66, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.46/0.66  cnf(c_0_67, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.46/0.66  cnf(c_0_68, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,k3_subset_1(X2,X3))), inference(spm,[status(thm)],[c_0_62, c_0_32])).
% 0.46/0.66  cnf(c_0_69, negated_conjecture, (r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(sr,[status(thm)],[c_0_63, c_0_64])).
% 0.46/0.66  cnf(c_0_70, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(er,[status(thm)],[c_0_65])).
% 0.46/0.66  cnf(c_0_71, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.46/0.66  cnf(c_0_72, negated_conjecture, (r1_tarski(esk3_0,k3_xboole_0(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_56]), c_0_70])])).
% 0.46/0.66  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_64]), ['proof']).
% 0.46/0.66  # SZS output end CNFRefutation
% 0.46/0.66  # Proof object total steps             : 74
% 0.46/0.66  # Proof object clause steps            : 41
% 0.46/0.66  # Proof object formula steps           : 33
% 0.46/0.66  # Proof object conjectures             : 16
% 0.46/0.66  # Proof object clause conjectures      : 13
% 0.46/0.66  # Proof object formula conjectures     : 3
% 0.46/0.66  # Proof object initial clauses used    : 19
% 0.46/0.66  # Proof object initial formulas used   : 16
% 0.46/0.66  # Proof object generating inferences   : 15
% 0.46/0.66  # Proof object simplifying inferences  : 19
% 0.46/0.66  # Training examples: 0 positive, 0 negative
% 0.46/0.66  # Parsed axioms                        : 16
% 0.46/0.66  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.66  # Initial clauses                      : 26
% 0.46/0.66  # Removed in clause preprocessing      : 3
% 0.46/0.66  # Initial clauses in saturation        : 23
% 0.46/0.66  # Processed clauses                    : 1539
% 0.46/0.66  # ...of these trivial                  : 73
% 0.46/0.66  # ...subsumed                          : 752
% 0.46/0.66  # ...remaining for further processing  : 714
% 0.46/0.66  # Other redundant clauses eliminated   : 0
% 0.46/0.66  # Clauses deleted for lack of memory   : 0
% 0.46/0.66  # Backward-subsumed                    : 59
% 0.46/0.66  # Backward-rewritten                   : 4
% 0.46/0.66  # Generated clauses                    : 13147
% 0.46/0.66  # ...of the previous two non-trivial   : 11892
% 0.46/0.66  # Contextual simplify-reflections      : 0
% 0.46/0.66  # Paramodulations                      : 13038
% 0.46/0.66  # Factorizations                       : 14
% 0.46/0.66  # Equation resolutions                 : 47
% 0.46/0.66  # Propositional unsat checks           : 0
% 0.46/0.66  #    Propositional check models        : 0
% 0.46/0.66  #    Propositional check unsatisfiable : 0
% 0.46/0.66  #    Propositional clauses             : 0
% 0.46/0.66  #    Propositional clauses after purity: 0
% 0.46/0.66  #    Propositional unsat core size     : 0
% 0.46/0.66  #    Propositional preprocessing time  : 0.000
% 0.46/0.66  #    Propositional encoding time       : 0.000
% 0.46/0.66  #    Propositional solver time         : 0.000
% 0.46/0.66  #    Success case prop preproc time    : 0.000
% 0.46/0.66  #    Success case prop encoding time   : 0.000
% 0.46/0.66  #    Success case prop solver time     : 0.000
% 0.46/0.66  # Current number of processed clauses  : 603
% 0.46/0.66  #    Positive orientable unit clauses  : 132
% 0.46/0.66  #    Positive unorientable unit clauses: 1
% 0.46/0.66  #    Negative unit clauses             : 2
% 0.46/0.66  #    Non-unit-clauses                  : 468
% 0.46/0.66  # Current number of unprocessed clauses: 10286
% 0.46/0.66  # ...number of literals in the above   : 29847
% 0.46/0.66  # Current number of archived formulas  : 0
% 0.46/0.66  # Current number of archived clauses   : 114
% 0.46/0.66  # Clause-clause subsumption calls (NU) : 43554
% 0.46/0.66  # Rec. Clause-clause subsumption calls : 32601
% 0.46/0.66  # Non-unit clause-clause subsumptions  : 750
% 0.46/0.66  # Unit Clause-clause subsumption calls : 1683
% 0.46/0.66  # Rewrite failures with RHS unbound    : 0
% 0.46/0.66  # BW rewrite match attempts            : 394
% 0.46/0.66  # BW rewrite match successes           : 8
% 0.46/0.66  # Condensation attempts                : 0
% 0.46/0.66  # Condensation successes               : 0
% 0.46/0.66  # Termbank termtop insertions          : 232280
% 0.46/0.66  
% 0.46/0.66  # -------------------------------------------------
% 0.46/0.66  # User time                : 0.300 s
% 0.46/0.66  # System time              : 0.015 s
% 0.46/0.66  # Total time               : 0.315 s
% 0.46/0.66  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
