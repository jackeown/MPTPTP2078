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
% DateTime   : Thu Dec  3 10:45:41 EST 2020

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   96 (6620 expanded)
%              Number of clauses        :   75 (3061 expanded)
%              Number of leaves         :   10 (1709 expanded)
%              Depth                    :   19
%              Number of atoms          :  201 (14967 expanded)
%              Number of equality atoms :   55 (4785 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

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

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(c_0_10,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X17,X16)
        | r1_tarski(X17,X15)
        | X16 != k1_zfmisc_1(X15) )
      & ( ~ r1_tarski(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k1_zfmisc_1(X15) )
      & ( ~ r2_hidden(esk1_2(X19,X20),X20)
        | ~ r1_tarski(esk1_2(X19,X20),X19)
        | X20 = k1_zfmisc_1(X19) )
      & ( r2_hidden(esk1_2(X19,X20),X20)
        | r1_tarski(esk1_2(X19,X20),X19)
        | X20 = k1_zfmisc_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

fof(c_0_12,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_14,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k3_xboole_0(X8,X9) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_15,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_16,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | k3_subset_1(X24,X25) = k4_xboole_0(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_17,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X23,X22)
        | r2_hidden(X23,X22)
        | v1_xboole_0(X22) )
      & ( ~ r2_hidden(X23,X22)
        | m1_subset_1(X23,X22)
        | v1_xboole_0(X22) )
      & ( ~ m1_subset_1(X23,X22)
        | v1_xboole_0(X23)
        | ~ v1_xboole_0(X22) )
      & ( ~ v1_xboole_0(X23)
        | m1_subset_1(X23,X22)
        | ~ v1_xboole_0(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X26] : ~ v1_xboole_0(k1_zfmisc_1(X26)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(esk3_0,esk4_0)
      | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) )
    & ( r1_tarski(esk3_0,esk4_0)
      | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_32,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | r1_tarski(k4_xboole_0(X12,X11),k4_xboole_0(X12,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_22])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_28])).

cnf(c_0_39,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2))) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_34]),c_0_36])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X1))) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X1)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_22]),c_0_22])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2)
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X2))) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0))) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_23])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k3_subset_1(X1,X2)) = k5_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)),esk4_0)
    | ~ r1_tarski(k5_xboole_0(esk4_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k5_xboole_0(X1,X1),k5_xboole_0(X1,k3_xboole_0(X1,esk4_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk4_0)) = k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_47])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,X1),esk4_0)
    | ~ r1_tarski(k5_xboole_0(esk4_0,esk4_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,esk4_0),k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_43])])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk4_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)))
    | ~ r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk4_0) = esk4_0
    | ~ r1_tarski(k3_xboole_0(esk4_0,esk4_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_52]),c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_52]),c_0_55])])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,X1) = k3_xboole_0(X2,X1)
    | ~ r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_23])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk4_0,k5_xboole_0(esk4_0,k3_xboole_0(X1,esk4_0)))
    | ~ r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_24])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,X1) = k3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_23])).

cnf(c_0_63,negated_conjecture,
    ( k3_subset_1(esk4_0,k3_xboole_0(esk4_0,esk4_0)) = k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0))
    | ~ r1_tarski(k3_xboole_0(esk4_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_65,negated_conjecture,
    ( k5_xboole_0(esk4_0,esk4_0) = k3_xboole_0(X1,esk4_0)
    | ~ r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X1))
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_23])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_40])).

cnf(c_0_68,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0)) = k3_subset_1(esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_59])]),c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( k3_subset_1(esk4_0,esk4_0) = k3_xboole_0(X1,esk4_0)
    | ~ r1_tarski(X1,k3_subset_1(esk4_0,esk4_0))
    | ~ r1_tarski(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_41])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,esk2_0)),k5_xboole_0(X1,X1))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_43])).

cnf(c_0_72,negated_conjecture,
    ( k5_xboole_0(esk4_0,esk4_0) = k3_subset_1(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])])).

cnf(c_0_73,negated_conjecture,
    ( k3_subset_1(esk4_0,esk4_0) = k3_xboole_0(X1,esk4_0)
    | ~ r1_tarski(X1,k3_subset_1(esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_69])])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)),k3_subset_1(esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_24]),c_0_69])])).

cnf(c_0_75,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0))) = k3_subset_1(esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_24])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_subset_1(esk4_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_68])).

cnf(c_0_77,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2)
    | ~ m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_35])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X2))) = k3_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_35])).

cnf(c_0_79,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_75]),c_0_76])).

cnf(c_0_80,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_35])).

cnf(c_0_81,plain,
    ( k3_subset_1(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_subset_1(X1,X2))
    | ~ m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk4_0) = k3_subset_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_79]),c_0_31])])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_84,plain,
    ( r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_35])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_tarski(X3,k3_subset_1(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_46])).

cnf(c_0_87,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0)) = k3_subset_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_79]),c_0_31])])).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_82]),c_0_43])])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85]),c_0_31])])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_85]),c_0_28])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,X1))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])]),c_0_90]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:49:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.07/1.26  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 1.07/1.26  # and selection function SelectNewComplexAHPExceptRRHorn.
% 1.07/1.26  #
% 1.07/1.26  # Preprocessing time       : 0.028 s
% 1.07/1.26  # Presaturation interreduction done
% 1.07/1.26  
% 1.07/1.26  # Proof found!
% 1.07/1.26  # SZS status Theorem
% 1.07/1.26  # SZS output start CNFRefutation
% 1.07/1.26  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.07/1.26  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 1.07/1.26  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.07/1.26  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.07/1.26  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.07/1.26  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.07/1.26  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.07/1.26  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.07/1.26  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.07/1.26  fof(t34_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 1.07/1.26  fof(c_0_10, plain, ![X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X17,X16)|r1_tarski(X17,X15)|X16!=k1_zfmisc_1(X15))&(~r1_tarski(X18,X15)|r2_hidden(X18,X16)|X16!=k1_zfmisc_1(X15)))&((~r2_hidden(esk1_2(X19,X20),X20)|~r1_tarski(esk1_2(X19,X20),X19)|X20=k1_zfmisc_1(X19))&(r2_hidden(esk1_2(X19,X20),X20)|r1_tarski(esk1_2(X19,X20),X19)|X20=k1_zfmisc_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 1.07/1.26  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 1.07/1.26  fof(c_0_12, plain, ![X13, X14]:k4_xboole_0(X13,k4_xboole_0(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.07/1.26  fof(c_0_13, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.07/1.26  fof(c_0_14, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k3_xboole_0(X8,X9)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 1.07/1.26  fof(c_0_15, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.07/1.26  fof(c_0_16, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|k3_subset_1(X24,X25)=k4_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 1.07/1.26  fof(c_0_17, plain, ![X22, X23]:(((~m1_subset_1(X23,X22)|r2_hidden(X23,X22)|v1_xboole_0(X22))&(~r2_hidden(X23,X22)|m1_subset_1(X23,X22)|v1_xboole_0(X22)))&((~m1_subset_1(X23,X22)|v1_xboole_0(X23)|~v1_xboole_0(X22))&(~v1_xboole_0(X23)|m1_subset_1(X23,X22)|~v1_xboole_0(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 1.07/1.26  cnf(c_0_18, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.07/1.26  fof(c_0_19, plain, ![X26]:~v1_xboole_0(k1_zfmisc_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 1.07/1.26  fof(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))&(r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 1.07/1.26  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.07/1.26  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.07/1.26  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.07/1.26  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.07/1.26  cnf(c_0_25, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.07/1.26  cnf(c_0_26, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.07/1.26  cnf(c_0_27, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_18])).
% 1.07/1.26  cnf(c_0_28, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.07/1.26  cnf(c_0_29, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.07/1.26  cnf(c_0_30, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.07/1.26  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.07/1.26  fof(c_0_32, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|r1_tarski(k4_xboole_0(X12,X11),k4_xboole_0(X12,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).
% 1.07/1.26  cnf(c_0_33, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_22])).
% 1.07/1.26  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.07/1.26  cnf(c_0_35, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_25, c_0_22])).
% 1.07/1.26  cnf(c_0_36, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 1.07/1.26  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_29])).
% 1.07/1.26  cnf(c_0_38, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_28])).
% 1.07/1.26  cnf(c_0_39, plain, (r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.07/1.26  cnf(c_0_40, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2)))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.07/1.26  cnf(c_0_41, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_34]), c_0_36])).
% 1.07/1.26  cnf(c_0_42, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X1)))=X1|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_23])).
% 1.07/1.26  cnf(c_0_43, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.07/1.26  cnf(c_0_44, plain, (r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X1)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_22]), c_0_22])).
% 1.07/1.26  cnf(c_0_45, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.07/1.26  cnf(c_0_46, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X2)))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.07/1.26  cnf(c_0_47, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0)))=esk4_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.07/1.26  cnf(c_0_48, plain, (r1_tarski(k5_xboole_0(X1,X1),k5_xboole_0(X1,k3_xboole_0(X1,X2)))|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_44, c_0_23])).
% 1.07/1.26  cnf(c_0_49, plain, (k3_xboole_0(X1,k3_subset_1(X1,X2))=k5_xboole_0(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.07/1.26  cnf(c_0_50, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)),esk4_0)|~r1_tarski(k5_xboole_0(esk4_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_44, c_0_47])).
% 1.07/1.26  cnf(c_0_51, negated_conjecture, (r1_tarski(k5_xboole_0(X1,X1),k5_xboole_0(X1,k3_xboole_0(X1,esk4_0)))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_48, c_0_43])).
% 1.07/1.26  cnf(c_0_52, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk4_0))=k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_33, c_0_47])).
% 1.07/1.26  cnf(c_0_53, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_46, c_0_49])).
% 1.07/1.26  cnf(c_0_54, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,X1),esk4_0)|~r1_tarski(k5_xboole_0(esk4_0,esk4_0),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_50, c_0_33])).
% 1.07/1.26  cnf(c_0_55, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,esk4_0),k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_43])])).
% 1.07/1.26  cnf(c_0_56, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_33, c_0_24])).
% 1.07/1.26  cnf(c_0_57, negated_conjecture, (r1_tarski(esk4_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)))|~r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_47])).
% 1.07/1.26  cnf(c_0_58, negated_conjecture, (k3_xboole_0(esk4_0,esk4_0)=esk4_0|~r1_tarski(k3_xboole_0(esk4_0,esk4_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_52]), c_0_47])).
% 1.07/1.26  cnf(c_0_59, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_52]), c_0_55])])).
% 1.07/1.26  cnf(c_0_60, plain, (k5_xboole_0(X1,X1)=k3_xboole_0(X2,X1)|~r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_56, c_0_23])).
% 1.07/1.26  cnf(c_0_61, negated_conjecture, (r1_tarski(esk4_0,k5_xboole_0(esk4_0,k3_xboole_0(X1,esk4_0)))|~r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_24])).
% 1.07/1.26  cnf(c_0_62, plain, (k5_xboole_0(X1,X1)=k3_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_33, c_0_23])).
% 1.07/1.26  cnf(c_0_63, negated_conjecture, (k3_subset_1(esk4_0,k3_xboole_0(esk4_0,esk4_0))=k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0))|~r1_tarski(k3_xboole_0(esk4_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_52])).
% 1.07/1.26  cnf(c_0_64, negated_conjecture, (k3_xboole_0(esk4_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])])).
% 1.07/1.26  cnf(c_0_65, negated_conjecture, (k5_xboole_0(esk4_0,esk4_0)=k3_xboole_0(X1,esk4_0)|~r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 1.07/1.26  cnf(c_0_66, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X1))|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_44, c_0_23])).
% 1.07/1.26  cnf(c_0_67, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(X1,X1)|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_62, c_0_40])).
% 1.07/1.26  cnf(c_0_68, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0))=k3_subset_1(esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_59])]), c_0_64])).
% 1.07/1.26  cnf(c_0_69, negated_conjecture, (r1_tarski(esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_59, c_0_64])).
% 1.07/1.26  cnf(c_0_70, negated_conjecture, (k3_subset_1(esk4_0,esk4_0)=k3_xboole_0(X1,esk4_0)|~r1_tarski(X1,k3_subset_1(esk4_0,esk4_0))|~r1_tarski(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_65, c_0_41])).
% 1.07/1.26  cnf(c_0_71, negated_conjecture, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,esk2_0)),k5_xboole_0(X1,X1))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_66, c_0_43])).
% 1.07/1.26  cnf(c_0_72, negated_conjecture, (k5_xboole_0(esk4_0,esk4_0)=k3_subset_1(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])])).
% 1.07/1.26  cnf(c_0_73, negated_conjecture, (k3_subset_1(esk4_0,esk4_0)=k3_xboole_0(X1,esk4_0)|~r1_tarski(X1,k3_subset_1(esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_69])])).
% 1.07/1.26  cnf(c_0_74, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)),k3_subset_1(esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_24]), c_0_69])])).
% 1.07/1.26  cnf(c_0_75, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)))=k3_subset_1(esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_24])).
% 1.07/1.26  cnf(c_0_76, negated_conjecture, (k5_xboole_0(esk4_0,k3_subset_1(esk4_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[c_0_47, c_0_68])).
% 1.07/1.26  cnf(c_0_77, plain, (k3_subset_1(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)|~m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_35])).
% 1.07/1.26  cnf(c_0_78, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X2)))=k3_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_35])).
% 1.07/1.26  cnf(c_0_79, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_75]), c_0_76])).
% 1.07/1.26  cnf(c_0_80, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_subset_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_44, c_0_35])).
% 1.07/1.26  cnf(c_0_81, plain, (k3_subset_1(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k3_subset_1(X1,X2))|~m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 1.07/1.26  cnf(c_0_82, negated_conjecture, (k5_xboole_0(esk2_0,esk4_0)=k3_subset_1(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_79]), c_0_31])])).
% 1.07/1.26  cnf(c_0_83, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.07/1.26  cnf(c_0_84, plain, (r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_80, c_0_35])).
% 1.07/1.26  cnf(c_0_85, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.07/1.26  cnf(c_0_86, plain, (r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_tarski(X3,k3_subset_1(X2,X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_46])).
% 1.07/1.26  cnf(c_0_87, negated_conjecture, (k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0))=k3_subset_1(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_79]), c_0_31])])).
% 1.07/1.26  cnf(c_0_88, negated_conjecture, (k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_82]), c_0_43])])).
% 1.07/1.26  cnf(c_0_89, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.07/1.26  cnf(c_0_90, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85]), c_0_31])])).
% 1.07/1.26  cnf(c_0_91, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_85]), c_0_28])).
% 1.07/1.26  cnf(c_0_92, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,X1))|~r1_tarski(X1,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])).
% 1.07/1.26  cnf(c_0_93, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[c_0_89, c_0_90])).
% 1.07/1.26  cnf(c_0_94, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_37, c_0_91])).
% 1.07/1.26  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])]), c_0_90]), ['proof']).
% 1.07/1.26  # SZS output end CNFRefutation
% 1.07/1.26  # Proof object total steps             : 96
% 1.07/1.26  # Proof object clause steps            : 75
% 1.07/1.26  # Proof object formula steps           : 21
% 1.07/1.26  # Proof object conjectures             : 41
% 1.07/1.26  # Proof object clause conjectures      : 38
% 1.07/1.26  # Proof object formula conjectures     : 3
% 1.07/1.26  # Proof object initial clauses used    : 15
% 1.07/1.26  # Proof object initial formulas used   : 10
% 1.07/1.26  # Proof object generating inferences   : 51
% 1.07/1.26  # Proof object simplifying inferences  : 44
% 1.07/1.26  # Training examples: 0 positive, 0 negative
% 1.07/1.26  # Parsed axioms                        : 10
% 1.07/1.26  # Removed by relevancy pruning/SinE    : 0
% 1.07/1.26  # Initial clauses                      : 19
% 1.07/1.26  # Removed in clause preprocessing      : 1
% 1.07/1.26  # Initial clauses in saturation        : 18
% 1.07/1.26  # Processed clauses                    : 6348
% 1.07/1.26  # ...of these trivial                  : 122
% 1.07/1.26  # ...subsumed                          : 4697
% 1.07/1.26  # ...remaining for further processing  : 1529
% 1.07/1.26  # Other redundant clauses eliminated   : 0
% 1.07/1.26  # Clauses deleted for lack of memory   : 0
% 1.07/1.26  # Backward-subsumed                    : 160
% 1.07/1.26  # Backward-rewritten                   : 374
% 1.07/1.26  # Generated clauses                    : 99466
% 1.07/1.26  # ...of the previous two non-trivial   : 95400
% 1.07/1.26  # Contextual simplify-reflections      : 47
% 1.07/1.26  # Paramodulations                      : 99460
% 1.07/1.26  # Factorizations                       : 2
% 1.07/1.26  # Equation resolutions                 : 2
% 1.07/1.26  # Propositional unsat checks           : 0
% 1.07/1.26  #    Propositional check models        : 0
% 1.07/1.26  #    Propositional check unsatisfiable : 0
% 1.07/1.26  #    Propositional clauses             : 0
% 1.07/1.26  #    Propositional clauses after purity: 0
% 1.07/1.26  #    Propositional unsat core size     : 0
% 1.07/1.26  #    Propositional preprocessing time  : 0.000
% 1.07/1.26  #    Propositional encoding time       : 0.000
% 1.07/1.26  #    Propositional solver time         : 0.000
% 1.07/1.26  #    Success case prop preproc time    : 0.000
% 1.07/1.26  #    Success case prop encoding time   : 0.000
% 1.07/1.26  #    Success case prop solver time     : 0.000
% 1.07/1.26  # Current number of processed clauses  : 975
% 1.07/1.26  #    Positive orientable unit clauses  : 38
% 1.07/1.26  #    Positive unorientable unit clauses: 1
% 1.07/1.26  #    Negative unit clauses             : 22
% 1.07/1.26  #    Non-unit-clauses                  : 914
% 1.07/1.26  # Current number of unprocessed clauses: 88059
% 1.07/1.26  # ...number of literals in the above   : 368475
% 1.07/1.26  # Current number of archived formulas  : 0
% 1.07/1.26  # Current number of archived clauses   : 555
% 1.07/1.26  # Clause-clause subsumption calls (NU) : 112754
% 1.07/1.26  # Rec. Clause-clause subsumption calls : 93595
% 1.07/1.26  # Non-unit clause-clause subsumptions  : 3071
% 1.07/1.26  # Unit Clause-clause subsumption calls : 4138
% 1.07/1.26  # Rewrite failures with RHS unbound    : 0
% 1.07/1.26  # BW rewrite match attempts            : 45
% 1.07/1.26  # BW rewrite match successes           : 34
% 1.07/1.26  # Condensation attempts                : 0
% 1.07/1.26  # Condensation successes               : 0
% 1.07/1.26  # Termbank termtop insertions          : 1864154
% 1.07/1.27  
% 1.07/1.27  # -------------------------------------------------
% 1.07/1.27  # User time                : 0.884 s
% 1.07/1.27  # System time              : 0.042 s
% 1.07/1.27  # Total time               : 0.926 s
% 1.07/1.27  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
