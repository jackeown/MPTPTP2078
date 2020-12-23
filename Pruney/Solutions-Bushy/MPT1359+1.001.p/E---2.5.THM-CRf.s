%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1359+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:11 EST 2020

% Result     : Theorem 0.07s
% Output     : CNFRefutation 0.07s
% Verified   : 
% Statistics : Number of formulae       :   69 (1451 expanded)
%              Number of clauses        :   56 ( 497 expanded)
%              Number of leaves         :    6 ( 354 expanded)
%              Depth                    :   13
%              Number of atoms          :  319 (22154 expanded)
%              Number of equality atoms :   91 (6460 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   47 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_compts_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_compts_1(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ~ ( X2 != k1_xboole_0
                & v2_tops_2(X2,X1)
                & k6_setfam_1(u1_struct_0(X1),X2) = k1_xboole_0
                & ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ~ ( X3 != k1_xboole_0
                        & r1_tarski(X3,X2)
                        & v1_finset_1(X3)
                        & k6_setfam_1(u1_struct_0(X1),X3) = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_compts_1)).

fof(t13_compts_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_compts_1(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ~ ( v3_finset_1(X2)
                & v2_tops_2(X2,X1)
                & k6_setfam_1(u1_struct_0(X1),X2) = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_compts_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(d3_finset_1,axiom,(
    ! [X1] :
      ( v3_finset_1(X1)
    <=> ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( X2 != k1_xboole_0
              & r1_tarski(X2,X1)
              & v1_finset_1(X2)
              & k1_setfam_1(X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_finset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ( v1_compts_1(X1)
        <=> ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ~ ( X2 != k1_xboole_0
                  & v2_tops_2(X2,X1)
                  & k6_setfam_1(u1_struct_0(X1),X2) = k1_xboole_0
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                     => ~ ( X3 != k1_xboole_0
                          & r1_tarski(X3,X2)
                          & v1_finset_1(X3)
                          & k6_setfam_1(u1_struct_0(X1),X3) = k1_xboole_0 ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t14_compts_1])).

fof(c_0_7,plain,(
    ! [X10,X11] :
      ( ( ~ v1_compts_1(X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ v3_finset_1(X11)
        | ~ v2_tops_2(X11,X10)
        | k6_setfam_1(u1_struct_0(X10),X11) != k1_xboole_0
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk2_1(X10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | v1_compts_1(X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v3_finset_1(esk2_1(X10))
        | v1_compts_1(X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v2_tops_2(esk2_1(X10),X10)
        | v1_compts_1(X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( k6_setfam_1(u1_struct_0(X10),esk2_1(X10)) = k1_xboole_0
        | v1_compts_1(X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_compts_1])])])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X20,X21] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
        | ~ v1_compts_1(esk3_0) )
      & ( esk4_0 != k1_xboole_0
        | ~ v1_compts_1(esk3_0) )
      & ( v2_tops_2(esk4_0,esk3_0)
        | ~ v1_compts_1(esk3_0) )
      & ( k6_setfam_1(u1_struct_0(esk3_0),esk4_0) = k1_xboole_0
        | ~ v1_compts_1(esk3_0) )
      & ( ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
        | X20 = k1_xboole_0
        | ~ r1_tarski(X20,esk4_0)
        | ~ v1_finset_1(X20)
        | k6_setfam_1(u1_struct_0(esk3_0),X20) != k1_xboole_0
        | ~ v1_compts_1(esk3_0) )
      & ( m1_subset_1(esk5_1(X21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
        | X21 = k1_xboole_0
        | ~ v2_tops_2(X21,esk3_0)
        | k6_setfam_1(u1_struct_0(esk3_0),X21) != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
        | v1_compts_1(esk3_0) )
      & ( esk5_1(X21) != k1_xboole_0
        | X21 = k1_xboole_0
        | ~ v2_tops_2(X21,esk3_0)
        | k6_setfam_1(u1_struct_0(esk3_0),X21) != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
        | v1_compts_1(esk3_0) )
      & ( r1_tarski(esk5_1(X21),X21)
        | X21 = k1_xboole_0
        | ~ v2_tops_2(X21,esk3_0)
        | k6_setfam_1(u1_struct_0(esk3_0),X21) != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
        | v1_compts_1(esk3_0) )
      & ( v1_finset_1(esk5_1(X21))
        | X21 = k1_xboole_0
        | ~ v2_tops_2(X21,esk3_0)
        | k6_setfam_1(u1_struct_0(esk3_0),X21) != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
        | v1_compts_1(esk3_0) )
      & ( k6_setfam_1(u1_struct_0(esk3_0),esk5_1(X21)) = k1_xboole_0
        | X21 = k1_xboole_0
        | ~ v2_tops_2(X21,esk3_0)
        | k6_setfam_1(u1_struct_0(esk3_0),X21) != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
        | v1_compts_1(esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])])).

fof(c_0_9,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v1_compts_1(esk3_0)
    | m1_subset_1(esk2_1(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_17,plain,
    ( v2_tops_2(esk2_1(X1),X1)
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( k6_setfam_1(u1_struct_0(X1),esk2_1(X1)) = k1_xboole_0
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_19,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8)))
      | k6_setfam_1(X8,X9) = k1_setfam_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v1_compts_1(esk3_0)
    | r1_tarski(esk2_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk5_1(X1),X1)
    | X1 = k1_xboole_0
    | v1_compts_1(esk3_0)
    | ~ v2_tops_2(X1,esk3_0)
    | k6_setfam_1(u1_struct_0(esk3_0),X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( v2_tops_2(esk2_1(esk3_0),esk3_0)
    | v1_compts_1(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk3_0),esk2_1(esk3_0)) = k1_xboole_0
    | v1_compts_1(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_11]),c_0_12])]),c_0_13])).

fof(c_0_25,plain,(
    ! [X4,X5,X6] :
      ( ( X4 != k1_xboole_0
        | ~ v3_finset_1(X4) )
      & ( X5 = k1_xboole_0
        | ~ r1_tarski(X5,X4)
        | ~ v1_finset_1(X5)
        | k1_setfam_1(X5) != k1_xboole_0
        | ~ v3_finset_1(X4) )
      & ( esk1_1(X6) != k1_xboole_0
        | X6 = k1_xboole_0
        | v3_finset_1(X6) )
      & ( r1_tarski(esk1_1(X6),X6)
        | X6 = k1_xboole_0
        | v3_finset_1(X6) )
      & ( v1_finset_1(esk1_1(X6))
        | X6 = k1_xboole_0
        | v3_finset_1(X6) )
      & ( k1_setfam_1(esk1_1(X6)) = k1_xboole_0
        | X6 = k1_xboole_0
        | v3_finset_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_finset_1])])])])])])).

cnf(c_0_26,plain,
    ( v3_finset_1(esk2_1(X1))
    | v1_compts_1(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( v1_finset_1(esk5_1(X1))
    | X1 = k1_xboole_0
    | v1_compts_1(esk3_0)
    | ~ v2_tops_2(X1,esk3_0)
    | k6_setfam_1(u1_struct_0(esk3_0),X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_compts_1(esk3_0)
    | esk5_1(X1) != k1_xboole_0
    | ~ v2_tops_2(X1,esk3_0)
    | k6_setfam_1(u1_struct_0(esk3_0),X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( v1_compts_1(esk3_0)
    | r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk2_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( esk2_1(esk3_0) = k1_xboole_0
    | v1_compts_1(esk3_0)
    | r1_tarski(esk5_1(esk2_1(esk3_0)),esk2_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_23]),c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    | ~ v1_compts_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ v1_finset_1(X1)
    | k1_setfam_1(X1) != k1_xboole_0
    | ~ v3_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( v1_compts_1(esk3_0)
    | v3_finset_1(esk2_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( esk2_1(esk3_0) = k1_xboole_0
    | v1_compts_1(esk3_0)
    | v1_finset_1(esk5_1(esk2_1(esk3_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_16]),c_0_23]),c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( esk2_1(esk3_0) = k1_xboole_0
    | v1_compts_1(esk3_0)
    | esk5_1(esk2_1(esk3_0)) != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_16]),c_0_23]),c_0_24])).

cnf(c_0_38,plain,
    ( k6_setfam_1(X1,X2) = k1_setfam_1(X2)
    | ~ r1_tarski(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( esk2_1(esk3_0) = k1_xboole_0
    | v1_compts_1(esk3_0)
    | r1_tarski(esk5_1(esk2_1(esk3_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk3_0),esk5_1(X1)) = k1_xboole_0
    | X1 = k1_xboole_0
    | v1_compts_1(esk3_0)
    | ~ v2_tops_2(X1,esk3_0)
    | k6_setfam_1(u1_struct_0(esk3_0),X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_compts_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( esk2_1(esk3_0) = k1_xboole_0
    | v1_compts_1(esk3_0)
    | k1_setfam_1(esk5_1(esk2_1(esk3_0))) != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k1_setfam_1(esk5_1(esk2_1(esk3_0))) = k6_setfam_1(u1_struct_0(esk3_0),esk5_1(esk2_1(esk3_0)))
    | esk2_1(esk3_0) = k1_xboole_0
    | v1_compts_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk3_0),esk5_1(esk2_1(esk3_0))) = k1_xboole_0
    | esk2_1(esk3_0) = k1_xboole_0
    | v1_compts_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_16]),c_0_23]),c_0_24])).

cnf(c_0_45,plain,
    ( X1 != k1_xboole_0
    | ~ v3_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    | ~ r1_tarski(X1,esk4_0)
    | ~ v1_finset_1(X1)
    | k6_setfam_1(u1_struct_0(esk3_0),X1) != k1_xboole_0
    | ~ v1_compts_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_compts_1(esk3_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( esk2_1(esk3_0) = k1_xboole_0
    | v1_compts_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_49,plain,
    ( ~ v3_finset_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( X1 = k1_xboole_0
    | k6_setfam_1(u1_struct_0(esk3_0),X1) != k1_xboole_0
    | ~ v1_compts_1(esk3_0)
    | ~ v1_finset_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_30]),c_0_47])).

cnf(c_0_51,plain,
    ( v1_finset_1(esk1_1(X1))
    | X1 = k1_xboole_0
    | v3_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | v3_finset_1(X1)
    | esk1_1(X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_53,negated_conjecture,
    ( k1_setfam_1(X1) = k6_setfam_1(u1_struct_0(esk3_0),X1)
    | ~ v1_compts_1(esk3_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( v1_compts_1(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_48]),c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( X1 = k1_xboole_0
    | v3_finset_1(X1)
    | k6_setfam_1(u1_struct_0(esk3_0),esk1_1(X1)) != k1_xboole_0
    | ~ v1_compts_1(esk3_0)
    | ~ r1_tarski(esk1_1(X1),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | ~ v1_compts_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v3_finset_1(X2)
    | ~ v2_tops_2(X2,X1)
    | k6_setfam_1(u1_struct_0(X1),X2) != k1_xboole_0
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_57,negated_conjecture,
    ( v2_tops_2(esk4_0,esk3_0)
    | ~ v1_compts_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_58,negated_conjecture,
    ( k6_setfam_1(u1_struct_0(esk3_0),esk4_0) = k1_xboole_0
    | ~ v1_compts_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_59,plain,
    ( k1_setfam_1(esk1_1(X1)) = k1_xboole_0
    | X1 = k1_xboole_0
    | v3_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_60,negated_conjecture,
    ( k1_setfam_1(X1) = k6_setfam_1(u1_struct_0(esk3_0),X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_61,negated_conjecture,
    ( X1 = k1_xboole_0
    | v3_finset_1(X1)
    | k6_setfam_1(u1_struct_0(esk3_0),esk1_1(X1)) != k1_xboole_0
    | ~ r1_tarski(esk1_1(X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_54])])).

cnf(c_0_62,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ v1_compts_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_compts_1(esk3_0)
    | ~ v3_finset_1(esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_33]),c_0_11]),c_0_12])]),c_0_13]),c_0_57]),c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( X1 = k1_xboole_0
    | v3_finset_1(X1)
    | ~ r1_tarski(esk1_1(X1),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_65,plain,
    ( r1_tarski(esk1_1(X1),X1)
    | X1 = k1_xboole_0
    | v3_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_54])])).

cnf(c_0_67,negated_conjecture,
    ( ~ v3_finset_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_54])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67]),
    [proof]).

%------------------------------------------------------------------------------
