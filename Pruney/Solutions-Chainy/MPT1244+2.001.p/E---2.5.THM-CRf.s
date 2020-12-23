%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:11:03 EST 2020

% Result     : Theorem 0.49s
% Output     : CNFRefutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 581 expanded)
%              Number of clauses        :   47 ( 251 expanded)
%              Number of leaves         :   10 ( 155 expanded)
%              Depth                    :   17
%              Number of atoms          :  261 (2113 expanded)
%              Number of equality atoms :   37 ( 277 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(projectivity_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(t49_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(t58_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,k1_tops_1(X1,X2)) = k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tops_1)).

fof(projectivity_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(c_0_10,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,plain,(
    ! [X21,X22,X23] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ r1_tarski(X22,X23)
      | r1_tarski(k1_tops_1(X21,X22),k1_tops_1(X21,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

fof(c_0_12,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | k1_tops_1(X17,k1_tops_1(X17,X18)) = k1_tops_1(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).

fof(c_0_13,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | m1_subset_1(k1_tops_1(X15,X16),k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,X2)) = k1_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k1_tops_1(X1,X2) = k1_tops_1(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k1_tops_1(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

fof(c_0_20,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | r1_tarski(k1_tops_1(X19,X20),X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_21,plain,
    ( k1_tops_1(X1,X2) = k1_tops_1(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( k1_tops_1(X1,k1_tops_1(X2,k1_tops_1(X1,X3))) = k1_tops_1(X1,X3)
    | ~ m1_subset_1(k1_tops_1(X2,k1_tops_1(X1,X3)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_tops_1(X1,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X3,k1_tops_1(X2,k1_tops_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_24,plain,(
    ! [X12,X13,X14] :
      ( ~ l1_pre_topc(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ r1_tarski(X13,X14)
      | r1_tarski(k2_pre_topc(X12,X13),k2_pre_topc(X12,X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).

cnf(c_0_25,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,k1_tops_1(X1,X2))) = k1_tops_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k1_tops_1(X1,k1_tops_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_17]),c_0_17])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( k1_tops_1(X1,X2) = k1_tops_1(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ r1_tarski(X3,k1_tops_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_19])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k1_tops_1(X1,X2),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,k1_tops_1(X1,X2))) = k1_tops_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,k1_tops_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_16]),c_0_17])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k1_tops_1(X1,X2) = k1_tops_1(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X3,k1_tops_1(X1,X2))
    | ~ r1_tarski(k1_tops_1(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => k2_pre_topc(X1,k1_tops_1(X1,X2)) = k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2)))) ) ) ),
    inference(assume_negation,[status(cth)],[t58_tops_1])).

cnf(c_0_34,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_29])).

cnf(c_0_35,plain,
    ( k1_tops_1(X1,k1_tops_1(X1,k1_tops_1(X1,X2))) = k1_tops_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_28]),c_0_31])]),c_0_17])).

fof(c_0_36,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
      | k2_pre_topc(X8,k2_pre_topc(X8,X9)) = k2_pre_topc(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).

fof(c_0_37,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | m1_subset_1(k2_pre_topc(X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_38,plain,
    ( k1_tops_1(X1,X2) = k1_tops_1(X1,k1_tops_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_15]),c_0_17])).

fof(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)) != k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

cnf(c_0_40,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_29])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ m1_subset_1(k1_tops_1(X1,k1_tops_1(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k1_tops_1(X1,k1_tops_1(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_35])).

cnf(c_0_42,plain,
    ( k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k1_tops_1(X1,X2) = k1_tops_1(X1,k1_tops_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( k2_pre_topc(X1,k1_tops_1(X1,X2)) = k2_pre_topc(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X3,k1_tops_1(X1,X2))
    | ~ r1_tarski(k1_tops_1(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_17])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k1_tops_1(X1,k1_tops_1(X1,X2)),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_17]),c_0_17])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_42]),c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k1_tops_1(esk1_0,k1_tops_1(esk1_0,X1)) = k1_tops_1(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_51,plain,
    ( k2_pre_topc(X1,k1_tops_1(X1,X2)) = k2_pre_topc(X1,k1_tops_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_15]),c_0_17])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,k1_tops_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_22]),c_0_17])).

cnf(c_0_53,plain,
    ( k2_pre_topc(X1,X2) = k2_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_50]),c_0_46])])).

cnf(c_0_55,plain,
    ( k2_pre_topc(X1,k1_tops_1(X1,k1_tops_1(X1,X2))) = k2_pre_topc(X1,k1_tops_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_22]),c_0_17])).

cnf(c_0_56,plain,
    ( k2_pre_topc(X1,k1_tops_1(X2,k2_pre_topc(X1,X3))) = k2_pre_topc(X1,X3)
    | ~ m1_subset_1(k1_tops_1(X2,k2_pre_topc(X1,X3)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_pre_topc(X1,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X3,k1_tops_1(X2,k2_pre_topc(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0)) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_45]),c_0_31])])).

cnf(c_0_58,plain,
    ( m1_subset_1(k2_pre_topc(X1,k1_tops_1(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_tops_1(X1,k1_tops_1(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_55])).

cnf(c_0_59,plain,
    ( k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X2))) = k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,k1_tops_1(X1,k2_pre_topc(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_17]),c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_57]),c_0_45]),c_0_46])])).

cnf(c_0_61,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)) != k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_57]),c_0_57]),c_0_46])])).

fof(c_0_63,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | r1_tarski(X11,k2_pre_topc(X10,X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_64,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_46])]),c_0_61]),c_0_62])).

cnf(c_0_65,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_46])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_17]),c_0_45]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:34:24 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.49/0.67  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_TT_S0Y
% 0.49/0.67  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.49/0.67  #
% 0.49/0.67  # Preprocessing time       : 0.038 s
% 0.49/0.67  # Presaturation interreduction done
% 0.49/0.67  
% 0.49/0.67  # Proof found!
% 0.49/0.67  # SZS status Theorem
% 0.49/0.67  # SZS output start CNFRefutation
% 0.49/0.67  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.49/0.67  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.49/0.67  fof(projectivity_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 0.49/0.67  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.49/0.67  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.49/0.67  fof(t49_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 0.49/0.67  fof(t58_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,k1_tops_1(X1,X2))=k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tops_1)).
% 0.49/0.67  fof(projectivity_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 0.49/0.67  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.49/0.67  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.49/0.67  fof(c_0_10, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.49/0.67  fof(c_0_11, plain, ![X21, X22, X23]:(~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|(~r1_tarski(X22,X23)|r1_tarski(k1_tops_1(X21,X22),k1_tops_1(X21,X23)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.49/0.67  fof(c_0_12, plain, ![X17, X18]:(~l1_pre_topc(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|k1_tops_1(X17,k1_tops_1(X17,X18))=k1_tops_1(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k1_tops_1])])).
% 0.49/0.67  fof(c_0_13, plain, ![X15, X16]:(~l1_pre_topc(X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|m1_subset_1(k1_tops_1(X15,X16),k1_zfmisc_1(u1_struct_0(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.49/0.67  cnf(c_0_14, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.49/0.67  cnf(c_0_15, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.49/0.67  cnf(c_0_16, plain, (k1_tops_1(X1,k1_tops_1(X1,X2))=k1_tops_1(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.49/0.67  cnf(c_0_17, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.49/0.67  cnf(c_0_18, plain, (k1_tops_1(X1,X2)=k1_tops_1(X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.49/0.67  cnf(c_0_19, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(X2,k1_tops_1(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.49/0.67  fof(c_0_20, plain, ![X19, X20]:(~l1_pre_topc(X19)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|r1_tarski(k1_tops_1(X19,X20),X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.49/0.67  cnf(c_0_21, plain, (k1_tops_1(X1,X2)=k1_tops_1(X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(X2,k1_tops_1(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.49/0.67  cnf(c_0_22, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.49/0.67  cnf(c_0_23, plain, (k1_tops_1(X1,k1_tops_1(X2,k1_tops_1(X1,X3)))=k1_tops_1(X1,X3)|~m1_subset_1(k1_tops_1(X2,k1_tops_1(X1,X3)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_tops_1(X1,X3),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~r1_tarski(X3,k1_tops_1(X2,k1_tops_1(X1,X3)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.49/0.67  fof(c_0_24, plain, ![X12, X13, X14]:(~l1_pre_topc(X12)|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(~r1_tarski(X13,X14)|r1_tarski(k2_pre_topc(X12,X13),k2_pre_topc(X12,X14)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).
% 0.49/0.67  cnf(c_0_25, plain, (k1_tops_1(X1,k1_tops_1(X1,k1_tops_1(X1,X2)))=k1_tops_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(X2,k1_tops_1(X1,k1_tops_1(X1,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_17]), c_0_17])).
% 0.49/0.67  cnf(c_0_26, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.49/0.67  cnf(c_0_27, plain, (k1_tops_1(X1,X2)=k1_tops_1(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~r1_tarski(X3,k1_tops_1(X1,X2))), inference(spm,[status(thm)],[c_0_14, c_0_19])).
% 0.49/0.67  cnf(c_0_28, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k1_tops_1(X1,X2),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.49/0.67  cnf(c_0_29, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.49/0.67  cnf(c_0_30, plain, (k1_tops_1(X1,k1_tops_1(X1,k1_tops_1(X1,X2)))=k1_tops_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,k1_tops_1(X1,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_16]), c_0_17])).
% 0.49/0.67  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_26])).
% 0.49/0.67  cnf(c_0_32, plain, (k1_tops_1(X1,X2)=k1_tops_1(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(X3,k1_tops_1(X1,X2))|~r1_tarski(k1_tops_1(X1,X2),X3)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.49/0.67  fof(c_0_33, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,k1_tops_1(X1,X2))=k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,k1_tops_1(X1,X2))))))), inference(assume_negation,[status(cth)],[t58_tops_1])).
% 0.49/0.67  cnf(c_0_34, plain, (k2_pre_topc(X1,X2)=k2_pre_topc(X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_14, c_0_29])).
% 0.49/0.67  cnf(c_0_35, plain, (k1_tops_1(X1,k1_tops_1(X1,k1_tops_1(X1,X2)))=k1_tops_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_28]), c_0_31])]), c_0_17])).
% 0.49/0.67  fof(c_0_36, plain, ![X8, X9]:(~l1_pre_topc(X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|k2_pre_topc(X8,k2_pre_topc(X8,X9))=k2_pre_topc(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[projectivity_k2_pre_topc])])).
% 0.49/0.67  fof(c_0_37, plain, ![X6, X7]:(~l1_pre_topc(X6)|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))|m1_subset_1(k2_pre_topc(X6,X7),k1_zfmisc_1(u1_struct_0(X6)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.49/0.67  cnf(c_0_38, plain, (k1_tops_1(X1,X2)=k1_tops_1(X1,k1_tops_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~r1_tarski(X3,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_15]), c_0_17])).
% 0.49/0.67  fof(c_0_39, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))!=k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 0.49/0.67  cnf(c_0_40, plain, (k2_pre_topc(X1,X2)=k2_pre_topc(X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(X3,X2)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_34, c_0_29])).
% 0.49/0.67  cnf(c_0_41, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~m1_subset_1(k1_tops_1(X1,k1_tops_1(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k1_tops_1(X1,k1_tops_1(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_15, c_0_35])).
% 0.49/0.67  cnf(c_0_42, plain, (k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_pre_topc(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.49/0.67  cnf(c_0_43, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.49/0.67  cnf(c_0_44, plain, (k1_tops_1(X1,X2)=k1_tops_1(X1,k1_tops_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(X3,X2)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_38, c_0_15])).
% 0.49/0.67  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.49/0.67  cnf(c_0_46, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.49/0.67  cnf(c_0_47, plain, (k2_pre_topc(X1,k1_tops_1(X1,X2))=k2_pre_topc(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(X3,k1_tops_1(X1,X2))|~r1_tarski(k1_tops_1(X1,X2),X3)), inference(spm,[status(thm)],[c_0_40, c_0_17])).
% 0.49/0.67  cnf(c_0_48, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k1_tops_1(X1,k1_tops_1(X1,X2)),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_17]), c_0_17])).
% 0.49/0.67  cnf(c_0_49, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(X2,k2_pre_topc(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_42]), c_0_43])).
% 0.49/0.67  cnf(c_0_50, negated_conjecture, (k1_tops_1(esk1_0,k1_tops_1(esk1_0,X1))=k1_tops_1(esk1_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.49/0.67  cnf(c_0_51, plain, (k2_pre_topc(X1,k1_tops_1(X1,X2))=k2_pre_topc(X1,k1_tops_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~r1_tarski(X3,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_15]), c_0_17])).
% 0.49/0.67  cnf(c_0_52, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,k1_tops_1(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_22]), c_0_17])).
% 0.49/0.67  cnf(c_0_53, plain, (k2_pre_topc(X1,X2)=k2_pre_topc(X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(X2,k2_pre_topc(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_34, c_0_49])).
% 0.49/0.67  cnf(c_0_54, negated_conjecture, (k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_50]), c_0_46])])).
% 0.49/0.67  cnf(c_0_55, plain, (k2_pre_topc(X1,k1_tops_1(X1,k1_tops_1(X1,X2)))=k2_pre_topc(X1,k1_tops_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_22]), c_0_17])).
% 0.49/0.67  cnf(c_0_56, plain, (k2_pre_topc(X1,k1_tops_1(X2,k2_pre_topc(X1,X3)))=k2_pre_topc(X1,X3)|~m1_subset_1(k1_tops_1(X2,k2_pre_topc(X1,X3)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k2_pre_topc(X1,X3),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~r1_tarski(X3,k1_tops_1(X2,k2_pre_topc(X1,X3)))), inference(spm,[status(thm)],[c_0_53, c_0_22])).
% 0.49/0.67  cnf(c_0_57, negated_conjecture, (k1_tops_1(esk1_0,k1_tops_1(esk1_0,esk2_0))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_45]), c_0_31])])).
% 0.49/0.67  cnf(c_0_58, plain, (m1_subset_1(k2_pre_topc(X1,k1_tops_1(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(k1_tops_1(X1,k1_tops_1(X1,X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_43, c_0_55])).
% 0.49/0.67  cnf(c_0_59, plain, (k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X2)))=k2_pre_topc(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~r1_tarski(X2,k1_tops_1(X1,k2_pre_topc(X1,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_17]), c_0_43])).
% 0.49/0.67  cnf(c_0_60, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_57]), c_0_45]), c_0_46])])).
% 0.49/0.67  cnf(c_0_61, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))!=k2_pre_topc(esk1_0,k1_tops_1(esk1_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.49/0.67  cnf(c_0_62, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_57]), c_0_57]), c_0_46])])).
% 0.49/0.67  fof(c_0_63, plain, ![X10, X11]:(~l1_pre_topc(X10)|(~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|r1_tarski(X11,k2_pre_topc(X10,X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.49/0.67  cnf(c_0_64, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk2_0),k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk2_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_46])]), c_0_61]), c_0_62])).
% 0.49/0.67  cnf(c_0_65, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.49/0.67  cnf(c_0_66, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_46])])).
% 0.49/0.67  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_17]), c_0_45]), c_0_46])]), ['proof']).
% 0.49/0.67  # SZS output end CNFRefutation
% 0.49/0.67  # Proof object total steps             : 68
% 0.49/0.67  # Proof object clause steps            : 47
% 0.49/0.67  # Proof object formula steps           : 21
% 0.49/0.67  # Proof object conjectures             : 14
% 0.49/0.67  # Proof object clause conjectures      : 11
% 0.49/0.67  # Proof object formula conjectures     : 3
% 0.49/0.67  # Proof object initial clauses used    : 13
% 0.49/0.67  # Proof object initial formulas used   : 10
% 0.49/0.67  # Proof object generating inferences   : 33
% 0.49/0.67  # Proof object simplifying inferences  : 37
% 0.49/0.67  # Training examples: 0 positive, 0 negative
% 0.49/0.67  # Parsed axioms                        : 10
% 0.49/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.49/0.67  # Initial clauses                      : 14
% 0.49/0.67  # Removed in clause preprocessing      : 0
% 0.49/0.67  # Initial clauses in saturation        : 14
% 0.49/0.67  # Processed clauses                    : 2058
% 0.49/0.67  # ...of these trivial                  : 13
% 0.49/0.67  # ...subsumed                          : 1523
% 0.49/0.67  # ...remaining for further processing  : 522
% 0.49/0.67  # Other redundant clauses eliminated   : 2
% 0.49/0.67  # Clauses deleted for lack of memory   : 0
% 0.49/0.67  # Backward-subsumed                    : 153
% 0.49/0.67  # Backward-rewritten                   : 60
% 0.49/0.67  # Generated clauses                    : 14532
% 0.49/0.67  # ...of the previous two non-trivial   : 13186
% 0.49/0.67  # Contextual simplify-reflections      : 81
% 0.49/0.67  # Paramodulations                      : 14530
% 0.49/0.67  # Factorizations                       : 0
% 0.49/0.67  # Equation resolutions                 : 2
% 0.49/0.67  # Propositional unsat checks           : 0
% 0.49/0.67  #    Propositional check models        : 0
% 0.49/0.67  #    Propositional check unsatisfiable : 0
% 0.49/0.67  #    Propositional clauses             : 0
% 0.49/0.67  #    Propositional clauses after purity: 0
% 0.49/0.67  #    Propositional unsat core size     : 0
% 0.49/0.67  #    Propositional preprocessing time  : 0.000
% 0.49/0.67  #    Propositional encoding time       : 0.000
% 0.49/0.67  #    Propositional solver time         : 0.000
% 0.49/0.67  #    Success case prop preproc time    : 0.000
% 0.49/0.67  #    Success case prop encoding time   : 0.000
% 0.49/0.67  #    Success case prop solver time     : 0.000
% 0.49/0.67  # Current number of processed clauses  : 294
% 0.49/0.67  #    Positive orientable unit clauses  : 17
% 0.49/0.67  #    Positive unorientable unit clauses: 0
% 0.49/0.67  #    Negative unit clauses             : 4
% 0.49/0.67  #    Non-unit-clauses                  : 273
% 0.49/0.67  # Current number of unprocessed clauses: 10913
% 0.49/0.67  # ...number of literals in the above   : 73773
% 0.49/0.67  # Current number of archived formulas  : 0
% 0.49/0.67  # Current number of archived clauses   : 226
% 0.49/0.67  # Clause-clause subsumption calls (NU) : 29041
% 0.49/0.67  # Rec. Clause-clause subsumption calls : 7514
% 0.49/0.67  # Non-unit clause-clause subsumptions  : 1242
% 0.49/0.67  # Unit Clause-clause subsumption calls : 292
% 0.49/0.67  # Rewrite failures with RHS unbound    : 0
% 0.49/0.67  # BW rewrite match attempts            : 20
% 0.49/0.67  # BW rewrite match successes           : 7
% 0.49/0.67  # Condensation attempts                : 0
% 0.49/0.67  # Condensation successes               : 0
% 0.49/0.67  # Termbank termtop insertions          : 544195
% 0.49/0.67  
% 0.49/0.67  # -------------------------------------------------
% 0.49/0.67  # User time                : 0.317 s
% 0.49/0.67  # System time              : 0.010 s
% 0.49/0.67  # Total time               : 0.327 s
% 0.49/0.67  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
