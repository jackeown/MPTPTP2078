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
% DateTime   : Thu Dec  3 11:18:21 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 647 expanded)
%              Number of clauses        :   39 ( 231 expanded)
%              Number of leaves         :    9 ( 170 expanded)
%              Depth                    :   11
%              Number of atoms          :  319 (4668 expanded)
%              Number of equality atoms :   36 ( 458 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(d11_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = k8_tmap_1(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X4 = u1_struct_0(X2)
                     => X3 = k6_tmap_1(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(t115_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_pre_topc(X3,k8_tmap_1(X1,X2))
             => ( u1_struct_0(X3) = u1_struct_0(X2)
               => ( v1_tsep_1(X3,k8_tmap_1(X1,X2))
                  & m1_pre_topc(X3,k8_tmap_1(X1,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_tmap_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(t16_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( ( v1_tsep_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(t102_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r2_hidden(X2,k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

fof(c_0_9,plain,(
    ! [X18,X19] :
      ( ( u1_struct_0(k6_tmap_1(X18,X19)) = u1_struct_0(X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( u1_pre_topc(k6_tmap_1(X18,X19)) = k5_tmap_1(X18,X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_10,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_pre_topc(X24,X23)
      | m1_subset_1(u1_struct_0(X24),k1_zfmisc_1(u1_struct_0(X23))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_11,plain,(
    ! [X12,X13] :
      ( ( v1_pre_topc(k6_tmap_1(X12,X13))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) )
      & ( v2_pre_topc(k6_tmap_1(X12,X13))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) )
      & ( l1_pre_topc(k6_tmap_1(X12,X13))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

cnf(c_0_12,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X7,X8,X9,X10] :
      ( ( X9 != k8_tmap_1(X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X7)))
        | X10 != u1_struct_0(X8)
        | X9 = k6_tmap_1(X7,X10)
        | ~ v1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_pre_topc(X8,X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk1_3(X7,X8,X9),k1_zfmisc_1(u1_struct_0(X7)))
        | X9 = k8_tmap_1(X7,X8)
        | ~ v1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_pre_topc(X8,X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( esk1_3(X7,X8,X9) = u1_struct_0(X8)
        | X9 = k8_tmap_1(X7,X8)
        | ~ v1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_pre_topc(X8,X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( X9 != k6_tmap_1(X7,esk1_3(X7,X8,X9))
        | X9 = k8_tmap_1(X7,X8)
        | ~ v1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_pre_topc(X8,X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_16,plain,(
    ! [X14,X15] :
      ( ( v1_pre_topc(k8_tmap_1(X14,X15))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | ~ m1_pre_topc(X15,X14) )
      & ( v2_pre_topc(k8_tmap_1(X14,X15))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | ~ m1_pre_topc(X15,X14) )
      & ( l1_pre_topc(k8_tmap_1(X14,X15))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | ~ m1_pre_topc(X15,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

cnf(c_0_17,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_19,plain,
    ( X1 = k6_tmap_1(X2,X4)
    | v2_struct_0(X2)
    | X1 != k8_tmap_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != u1_struct_0(X3)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( m1_pre_topc(X3,k8_tmap_1(X1,X2))
               => ( u1_struct_0(X3) = u1_struct_0(X2)
                 => ( v1_tsep_1(X3,k8_tmap_1(X1,X2))
                    & m1_pre_topc(X3,k8_tmap_1(X1,X2)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t115_tmap_1])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,k6_tmap_1(X1,u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_17]),c_0_18])).

cnf(c_0_25,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])]),c_0_20]),c_0_13]),c_0_21]),c_0_22])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & m1_pre_topc(esk4_0,k8_tmap_1(esk2_0,esk3_0))
    & u1_struct_0(esk4_0) = u1_struct_0(esk3_0)
    & ( ~ v1_tsep_1(esk4_0,k8_tmap_1(esk2_0,esk3_0))
      | ~ m1_pre_topc(esk4_0,k8_tmap_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,k8_tmap_1(X1,X3))
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk4_0,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_34,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_36,plain,(
    ! [X5,X6] :
      ( ( ~ v3_pre_topc(X6,X5)
        | r2_hidden(X6,u1_pre_topc(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) )
      & ( ~ r2_hidden(X6,u1_pre_topc(X5))
        | v3_pre_topc(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_37,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk4_0))) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_33]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k6_tmap_1(X1,u1_struct_0(esk4_0)) = k8_tmap_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_33]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk4_0))) = k5_tmap_1(esk2_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_30]),c_0_31])]),c_0_32])).

fof(c_0_41,plain,(
    ! [X20,X21,X22] :
      ( ( ~ v1_tsep_1(X21,X20)
        | ~ m1_pre_topc(X21,X20)
        | v3_pre_topc(X22,X20)
        | X22 != u1_struct_0(X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_pre_topc(X21,X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( v1_tsep_1(X21,X20)
        | ~ v3_pre_topc(X22,X20)
        | X22 != u1_struct_0(X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_pre_topc(X21,X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_pre_topc(X21,X20)
        | ~ v3_pre_topc(X22,X20)
        | X22 != u1_struct_0(X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m1_pre_topc(X21,X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

cnf(c_0_42,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_38]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) = k5_tmap_1(esk2_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_38]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

fof(c_0_46,plain,(
    ! [X16,X17] :
      ( v2_struct_0(X16)
      | ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | r2_hidden(X17,k5_tmap_1(X16,X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t102_tmap_1])])])])).

cnf(c_0_47,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( v3_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ r2_hidden(X1,k5_tmap_1(esk2_0,u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_33]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_tsep_1(esk4_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(esk4_0,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_53,plain,
    ( v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_13])).

cnf(c_0_54,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk4_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_33]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_55,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_38]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_tsep_1(esk4_0,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_28])])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_28]),c_0_55]),c_0_44])]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.61/0.78  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.61/0.78  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.61/0.78  #
% 0.61/0.78  # Preprocessing time       : 0.028 s
% 0.61/0.78  
% 0.61/0.78  # Proof found!
% 0.61/0.78  # SZS status Theorem
% 0.61/0.78  # SZS output start CNFRefutation
% 0.61/0.78  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.61/0.78  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.61/0.78  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 0.61/0.78  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.61/0.78  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.61/0.78  fof(t115_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_pre_topc(X3,k8_tmap_1(X1,X2))=>(u1_struct_0(X3)=u1_struct_0(X2)=>(v1_tsep_1(X3,k8_tmap_1(X1,X2))&m1_pre_topc(X3,k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_tmap_1)).
% 0.61/0.78  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.61/0.78  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.61/0.78  fof(t102_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r2_hidden(X2,k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_tmap_1)).
% 0.61/0.78  fof(c_0_9, plain, ![X18, X19]:((u1_struct_0(k6_tmap_1(X18,X19))=u1_struct_0(X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(u1_pre_topc(k6_tmap_1(X18,X19))=k5_tmap_1(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.61/0.78  fof(c_0_10, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_pre_topc(X24,X23)|m1_subset_1(u1_struct_0(X24),k1_zfmisc_1(u1_struct_0(X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.61/0.78  fof(c_0_11, plain, ![X12, X13]:(((v1_pre_topc(k6_tmap_1(X12,X13))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))))&(v2_pre_topc(k6_tmap_1(X12,X13))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))))))&(l1_pre_topc(k6_tmap_1(X12,X13))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 0.61/0.78  cnf(c_0_12, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.61/0.78  cnf(c_0_13, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.61/0.78  cnf(c_0_14, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.61/0.78  fof(c_0_15, plain, ![X7, X8, X9, X10]:((X9!=k8_tmap_1(X7,X8)|(~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X7)))|(X10!=u1_struct_0(X8)|X9=k6_tmap_1(X7,X10)))|(~v1_pre_topc(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9))|~m1_pre_topc(X8,X7)|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)))&((m1_subset_1(esk1_3(X7,X8,X9),k1_zfmisc_1(u1_struct_0(X7)))|X9=k8_tmap_1(X7,X8)|(~v1_pre_topc(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9))|~m1_pre_topc(X8,X7)|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)))&((esk1_3(X7,X8,X9)=u1_struct_0(X8)|X9=k8_tmap_1(X7,X8)|(~v1_pre_topc(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9))|~m1_pre_topc(X8,X7)|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)))&(X9!=k6_tmap_1(X7,esk1_3(X7,X8,X9))|X9=k8_tmap_1(X7,X8)|(~v1_pre_topc(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9))|~m1_pre_topc(X8,X7)|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.61/0.78  fof(c_0_16, plain, ![X14, X15]:(((v1_pre_topc(k8_tmap_1(X14,X15))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)|~m1_pre_topc(X15,X14)))&(v2_pre_topc(k8_tmap_1(X14,X15))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)|~m1_pre_topc(X15,X14))))&(l1_pre_topc(k8_tmap_1(X14,X15))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)|~m1_pre_topc(X15,X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.61/0.78  cnf(c_0_17, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.61/0.78  cnf(c_0_18, plain, (v2_struct_0(X1)|l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_14, c_0_13])).
% 0.61/0.78  cnf(c_0_19, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.61/0.78  cnf(c_0_20, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.61/0.78  cnf(c_0_21, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.61/0.78  cnf(c_0_22, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.61/0.78  fof(c_0_23, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_pre_topc(X3,k8_tmap_1(X1,X2))=>(u1_struct_0(X3)=u1_struct_0(X2)=>(v1_tsep_1(X3,k8_tmap_1(X1,X2))&m1_pre_topc(X3,k8_tmap_1(X1,X2)))))))), inference(assume_negation,[status(cth)],[t115_tmap_1])).
% 0.61/0.78  cnf(c_0_24, plain, (v2_struct_0(X1)|m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,k6_tmap_1(X1,u1_struct_0(X3)))|~m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_17]), c_0_18])).
% 0.61/0.78  cnf(c_0_25, plain, (k6_tmap_1(X1,u1_struct_0(X2))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_19])]), c_0_20]), c_0_13]), c_0_21]), c_0_22])).
% 0.61/0.78  fof(c_0_26, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&(m1_pre_topc(esk4_0,k8_tmap_1(esk2_0,esk3_0))&(u1_struct_0(esk4_0)=u1_struct_0(esk3_0)&(~v1_tsep_1(esk4_0,k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(esk4_0,k8_tmap_1(esk2_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_23])])])])).
% 0.61/0.78  cnf(c_0_27, plain, (v2_struct_0(X1)|m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,k8_tmap_1(X1,X3))|~m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.61/0.78  cnf(c_0_28, negated_conjecture, (m1_pre_topc(esk4_0,k8_tmap_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.61/0.78  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.61/0.78  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.61/0.78  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.61/0.78  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.61/0.78  cnf(c_0_33, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.61/0.78  cnf(c_0_34, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.61/0.78  cnf(c_0_35, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.61/0.78  fof(c_0_36, plain, ![X5, X6]:((~v3_pre_topc(X6,X5)|r2_hidden(X6,u1_pre_topc(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5))&(~r2_hidden(X6,u1_pre_topc(X5))|v3_pre_topc(X6,X5)|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.61/0.78  cnf(c_0_37, negated_conjecture, (u1_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk4_0)))=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_33]), c_0_30]), c_0_31])]), c_0_32])).
% 0.61/0.78  cnf(c_0_38, negated_conjecture, (k6_tmap_1(X1,u1_struct_0(esk4_0))=k8_tmap_1(X1,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_25, c_0_34])).
% 0.61/0.78  cnf(c_0_39, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_33]), c_0_30]), c_0_31])]), c_0_32])).
% 0.61/0.78  cnf(c_0_40, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk4_0)))=k5_tmap_1(esk2_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_33]), c_0_30]), c_0_31])]), c_0_32])).
% 0.61/0.78  fof(c_0_41, plain, ![X20, X21, X22]:((~v1_tsep_1(X21,X20)|~m1_pre_topc(X21,X20)|v3_pre_topc(X22,X20)|X22!=u1_struct_0(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|~m1_pre_topc(X21,X20)|(~v2_pre_topc(X20)|~l1_pre_topc(X20)))&((v1_tsep_1(X21,X20)|~v3_pre_topc(X22,X20)|X22!=u1_struct_0(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|~m1_pre_topc(X21,X20)|(~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(m1_pre_topc(X21,X20)|~v3_pre_topc(X22,X20)|X22!=u1_struct_0(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|~m1_pre_topc(X21,X20)|(~v2_pre_topc(X20)|~l1_pre_topc(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.61/0.78  cnf(c_0_42, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.61/0.78  cnf(c_0_43, negated_conjecture, (u1_struct_0(k8_tmap_1(esk2_0,esk3_0))=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.61/0.78  cnf(c_0_44, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_38]), c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.61/0.78  cnf(c_0_45, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))=k5_tmap_1(esk2_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_38]), c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.61/0.78  fof(c_0_46, plain, ![X16, X17]:(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|r2_hidden(X17,k5_tmap_1(X16,X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t102_tmap_1])])])])).
% 0.61/0.78  cnf(c_0_47, plain, (v2_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.61/0.78  cnf(c_0_48, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.61/0.78  cnf(c_0_49, negated_conjecture, (v3_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))|~r2_hidden(X1,k5_tmap_1(esk2_0,u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])]), c_0_45])).
% 0.61/0.78  cnf(c_0_50, plain, (v2_struct_0(X1)|r2_hidden(X2,k5_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.61/0.78  cnf(c_0_51, negated_conjecture, (v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_33]), c_0_30]), c_0_31])]), c_0_32])).
% 0.61/0.78  cnf(c_0_52, negated_conjecture, (~v1_tsep_1(esk4_0,k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(esk4_0,k8_tmap_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.61/0.78  cnf(c_0_53, plain, (v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]), c_0_13])).
% 0.61/0.78  cnf(c_0_54, negated_conjecture, (v3_pre_topc(u1_struct_0(esk4_0),k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_33]), c_0_30]), c_0_31])]), c_0_32])).
% 0.61/0.78  cnf(c_0_55, negated_conjecture, (v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_38]), c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.61/0.78  cnf(c_0_56, negated_conjecture, (~v1_tsep_1(esk4_0,k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_28])])).
% 0.61/0.78  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_28]), c_0_55]), c_0_44])]), c_0_56]), ['proof']).
% 0.61/0.78  # SZS output end CNFRefutation
% 0.61/0.78  # Proof object total steps             : 58
% 0.61/0.78  # Proof object clause steps            : 39
% 0.61/0.78  # Proof object formula steps           : 19
% 0.61/0.78  # Proof object conjectures             : 24
% 0.61/0.78  # Proof object clause conjectures      : 21
% 0.61/0.78  # Proof object formula conjectures     : 3
% 0.61/0.78  # Proof object initial clauses used    : 19
% 0.61/0.78  # Proof object initial formulas used   : 9
% 0.61/0.78  # Proof object generating inferences   : 17
% 0.61/0.78  # Proof object simplifying inferences  : 65
% 0.61/0.78  # Training examples: 0 positive, 0 negative
% 0.61/0.78  # Parsed axioms                        : 9
% 0.61/0.78  # Removed by relevancy pruning/SinE    : 0
% 0.61/0.78  # Initial clauses                      : 27
% 0.61/0.78  # Removed in clause preprocessing      : 1
% 0.61/0.78  # Initial clauses in saturation        : 26
% 0.61/0.78  # Processed clauses                    : 2639
% 0.61/0.78  # ...of these trivial                  : 1
% 0.61/0.78  # ...subsumed                          : 1867
% 0.61/0.78  # ...remaining for further processing  : 771
% 0.61/0.78  # Other redundant clauses eliminated   : 5
% 0.61/0.78  # Clauses deleted for lack of memory   : 0
% 0.61/0.78  # Backward-subsumed                    : 28
% 0.61/0.78  # Backward-rewritten                   : 0
% 0.61/0.78  # Generated clauses                    : 15455
% 0.61/0.78  # ...of the previous two non-trivial   : 14748
% 0.61/0.78  # Contextual simplify-reflections      : 179
% 0.61/0.78  # Paramodulations                      : 15451
% 0.61/0.78  # Factorizations                       : 0
% 0.61/0.78  # Equation resolutions                 : 5
% 0.61/0.78  # Propositional unsat checks           : 0
% 0.61/0.78  #    Propositional check models        : 0
% 0.61/0.78  #    Propositional check unsatisfiable : 0
% 0.61/0.78  #    Propositional clauses             : 0
% 0.61/0.78  #    Propositional clauses after purity: 0
% 0.61/0.78  #    Propositional unsat core size     : 0
% 0.61/0.78  #    Propositional preprocessing time  : 0.000
% 0.61/0.78  #    Propositional encoding time       : 0.000
% 0.61/0.78  #    Propositional solver time         : 0.000
% 0.61/0.78  #    Success case prop preproc time    : 0.000
% 0.61/0.78  #    Success case prop encoding time   : 0.000
% 0.61/0.78  #    Success case prop solver time     : 0.000
% 0.61/0.78  # Current number of processed clauses  : 740
% 0.61/0.78  #    Positive orientable unit clauses  : 17
% 0.61/0.78  #    Positive unorientable unit clauses: 0
% 0.61/0.78  #    Negative unit clauses             : 3
% 0.61/0.78  #    Non-unit-clauses                  : 720
% 0.61/0.78  # Current number of unprocessed clauses: 12001
% 0.61/0.78  # ...number of literals in the above   : 127387
% 0.61/0.78  # Current number of archived formulas  : 0
% 0.61/0.78  # Current number of archived clauses   : 28
% 0.61/0.78  # Clause-clause subsumption calls (NU) : 327374
% 0.61/0.78  # Rec. Clause-clause subsumption calls : 11663
% 0.61/0.78  # Non-unit clause-clause subsumptions  : 2074
% 0.61/0.78  # Unit Clause-clause subsumption calls : 1
% 0.61/0.78  # Rewrite failures with RHS unbound    : 0
% 0.61/0.78  # BW rewrite match attempts            : 3
% 0.61/0.78  # BW rewrite match successes           : 0
% 0.61/0.78  # Condensation attempts                : 0
% 0.61/0.78  # Condensation successes               : 0
% 0.61/0.78  # Termbank termtop insertions          : 518293
% 0.61/0.78  
% 0.61/0.78  # -------------------------------------------------
% 0.61/0.78  # User time                : 0.429 s
% 0.61/0.78  # System time              : 0.010 s
% 0.61/0.78  # Total time               : 0.439 s
% 0.61/0.78  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
