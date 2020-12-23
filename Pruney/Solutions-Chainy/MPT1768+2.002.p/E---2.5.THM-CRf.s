%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:41 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   88 (1037 expanded)
%              Number of clauses        :   69 ( 347 expanded)
%              Number of leaves         :    9 ( 257 expanded)
%              Depth                    :   23
%              Number of atoms          :  477 (11366 expanded)
%              Number of equality atoms :   32 (  72 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X5,X4) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                           => r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tmap_1)).

fof(d4_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(dt_k2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & l1_struct_0(X4) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(d5_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(t78_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X3,X4)
                       => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( ~ v2_struct_0(X5)
                          & m1_pre_topc(X5,X1) )
                       => ( ( m1_pre_topc(X4,X3)
                            & m1_pre_topc(X5,X4) )
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                             => r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t79_tmap_1])).

fof(c_0_10,plain,(
    ! [X12,X13,X14,X15] :
      ( v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
      | ~ m1_pre_topc(X15,X12)
      | k2_tmap_1(X12,X13,X14,X15) = k2_partfun1(u1_struct_0(X12),u1_struct_0(X13),X14,u1_struct_0(X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

fof(c_0_11,plain,(
    ! [X21,X22,X23,X24] :
      ( ( v1_funct_1(k2_tmap_1(X21,X22,X23,X24))
        | ~ l1_struct_0(X21)
        | ~ l1_struct_0(X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | ~ l1_struct_0(X24) )
      & ( v1_funct_2(k2_tmap_1(X21,X22,X23,X24),u1_struct_0(X24),u1_struct_0(X22))
        | ~ l1_struct_0(X21)
        | ~ l1_struct_0(X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | ~ l1_struct_0(X24) )
      & ( m1_subset_1(k2_tmap_1(X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X22))))
        | ~ l1_struct_0(X21)
        | ~ l1_struct_0(X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
        | ~ l1_struct_0(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

fof(c_0_12,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & m1_pre_topc(esk5_0,esk4_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    & ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | l1_pre_topc(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_22,plain,
    ( k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X5)) = k2_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(k2_tmap_1(X3,X2,X4,X1))
    | ~ v1_funct_1(X4)
    | ~ l1_struct_0(X3)
    | ~ m1_pre_topc(X5,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( k2_partfun1(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),u1_struct_0(X2)) = k2_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,X1))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_18]),c_0_19]),c_0_20]),c_0_24]),c_0_25])]),c_0_26]),c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_32,negated_conjecture,
    ( k2_partfun1(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),u1_struct_0(X2)) = k2_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,X1))
    | ~ l1_struct_0(esk2_0)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_16]),c_0_31])])).

cnf(c_0_33,negated_conjecture,
    ( k2_partfun1(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),u1_struct_0(X2)) = k2_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_16]),c_0_24])])).

cnf(c_0_34,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( k2_partfun1(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),u1_struct_0(X2)) = k2_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_18]),c_0_19]),c_0_20])]),c_0_16])).

fof(c_0_36,plain,(
    ! [X7,X8] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X8,X7)
      | v2_pre_topc(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_37,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( v2_struct_0(X16)
      | ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X16)
      | ~ m1_pre_topc(X19,X16)
      | ~ v1_funct_1(X20)
      | ~ v1_funct_2(X20,u1_struct_0(X18),u1_struct_0(X17))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X17))))
      | ~ m1_pre_topc(X19,X18)
      | k3_tmap_1(X16,X17,X18,X19,X20) = k2_partfun1(u1_struct_0(X18),u1_struct_0(X17),X20,u1_struct_0(X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_38,plain,(
    ! [X30,X31,X32] :
      ( ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | ~ m1_pre_topc(X32,X31)
      | m1_pre_topc(X32,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_39,negated_conjecture,
    ( k2_partfun1(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),u1_struct_0(X2)) = k2_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_16]),c_0_24])])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k2_partfun1(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),u1_struct_0(X2)) = k2_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_16]),c_0_31])])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_40]),c_0_29])])).

cnf(c_0_48,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_29]),c_0_42])])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),u1_struct_0(esk5_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])]),c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_46]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,X1))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_54,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_16]),c_0_24])])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_57,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_29]),c_0_42])])).

cnf(c_0_58,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_16]),c_0_31])])).

cnf(c_0_59,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk2_0,esk6_0,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_18]),c_0_19]),c_0_20]),c_0_24]),c_0_25])]),c_0_26]),c_0_56]),c_0_31]),c_0_57])])).

cnf(c_0_60,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_16]),c_0_47])])).

fof(c_0_61,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X27,X25)
      | v2_struct_0(X28)
      | ~ m1_pre_topc(X28,X25)
      | ~ v1_funct_1(X29)
      | ~ v1_funct_2(X29,u1_struct_0(X25),u1_struct_0(X26))
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
      | ~ m1_pre_topc(X27,X28)
      | r2_funct_2(u1_struct_0(X27),u1_struct_0(X26),k3_tmap_1(X25,X26,X28,X27,k2_tmap_1(X25,X26,X29,X28)),k2_tmap_1(X25,X26,X29,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_tmap_1])])])])).

cnf(c_0_62,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,X2,esk6_0) = k2_tmap_1(esk3_0,esk2_0,esk6_0,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_59]),c_0_18]),c_0_19]),c_0_20]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_63,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_46])).

cnf(c_0_65,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_15]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk6_0) = k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_69,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_57]),c_0_63]),c_0_31])])).

cnf(c_0_70,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_16]),c_0_47])])).

cnf(c_0_71,plain,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,X4,X1,k2_tmap_1(X3,X2,X5,X4)),k2_tmap_1(X3,X2,X5,X1))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_66,c_0_44])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_73,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) = k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_28]),c_0_29]),c_0_42])]),c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,esk5_0,esk6_0) = k2_tmap_1(esk3_0,esk2_0,esk6_0,esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_16]),c_0_24])])).

cnf(c_0_76,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk3_0,esk2_0,X2,X1,k2_tmap_1(esk3_0,esk2_0,esk6_0,X2)),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_18]),c_0_19]),c_0_20]),c_0_24]),c_0_31]),c_0_25]),c_0_57])]),c_0_26]),c_0_56])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0) = k2_tmap_1(esk3_0,esk2_0,esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_28]),c_0_29]),c_0_42])]),c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_16]),c_0_31])])).

cnf(c_0_80,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk3_0,esk2_0,esk4_0,X1,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_63]),c_0_49])).

cnf(c_0_81,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)),k2_tmap_1(esk3_0,esk2_0,esk6_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_40]),c_0_29]),c_0_42])]),c_0_68])).

cnf(c_0_84,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)),k2_tmap_1(esk3_0,esk2_0,esk6_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_46]),c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_63]),c_0_31]),c_0_57])]),c_0_56])).

cnf(c_0_86,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85]),c_0_86]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:58:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.19/0.44  # and selection function PSelectComplexExceptRRHorn.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.028 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t79_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X4,X3)&m1_pre_topc(X5,X4))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tmap_1)).
% 0.19/0.44  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.19/0.44  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 0.19/0.44  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.44  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.44  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.19/0.44  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.19/0.44  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.19/0.44  fof(t78_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tmap_1)).
% 0.19/0.44  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X4,X3)&m1_pre_topc(X5,X4))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6)))))))))), inference(assume_negation,[status(cth)],[t79_tmap_1])).
% 0.19/0.44  fof(c_0_10, plain, ![X12, X13, X14, X15]:(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)|(~v1_funct_1(X14)|~v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))|(~m1_pre_topc(X15,X12)|k2_tmap_1(X12,X13,X14,X15)=k2_partfun1(u1_struct_0(X12),u1_struct_0(X13),X14,u1_struct_0(X15)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.19/0.44  fof(c_0_11, plain, ![X21, X22, X23, X24]:(((v1_funct_1(k2_tmap_1(X21,X22,X23,X24))|(~l1_struct_0(X21)|~l1_struct_0(X22)|~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))|~l1_struct_0(X24)))&(v1_funct_2(k2_tmap_1(X21,X22,X23,X24),u1_struct_0(X24),u1_struct_0(X22))|(~l1_struct_0(X21)|~l1_struct_0(X22)|~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))|~l1_struct_0(X24))))&(m1_subset_1(k2_tmap_1(X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X22))))|(~l1_struct_0(X21)|~l1_struct_0(X22)|~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))|~l1_struct_0(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 0.19/0.44  fof(c_0_12, plain, ![X9]:(~l1_pre_topc(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.44  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&((m1_pre_topc(esk4_0,esk3_0)&m1_pre_topc(esk5_0,esk4_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.19/0.44  cnf(c_0_14, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.44  cnf(c_0_15, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.44  cnf(c_0_16, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.44  cnf(c_0_17, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.44  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_19, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  fof(c_0_21, plain, ![X10, X11]:(~l1_pre_topc(X10)|(~m1_pre_topc(X11,X10)|l1_pre_topc(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.44  cnf(c_0_22, plain, (k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X5))=k2_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(k2_tmap_1(X3,X2,X4,X1))|~v1_funct_1(X4)|~l1_struct_0(X3)|~m1_pre_topc(X5,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_16])).
% 0.19/0.44  cnf(c_0_23, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.44  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_27, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.44  cnf(c_0_28, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_30, negated_conjecture, (k2_partfun1(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),u1_struct_0(X2))=k2_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),X2)|v2_struct_0(X1)|~v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,X1))|~l1_struct_0(esk3_0)|~l1_struct_0(esk2_0)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_18]), c_0_19]), c_0_20]), c_0_24]), c_0_25])]), c_0_26]), c_0_16])).
% 0.19/0.44  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.19/0.44  cnf(c_0_32, negated_conjecture, (k2_partfun1(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),u1_struct_0(X2))=k2_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),X2)|v2_struct_0(X1)|~v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,X1))|~l1_struct_0(esk2_0)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_16]), c_0_31])])).
% 0.19/0.44  cnf(c_0_33, negated_conjecture, (k2_partfun1(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),u1_struct_0(X2))=k2_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),X2)|v2_struct_0(X1)|~v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_16]), c_0_24])])).
% 0.19/0.44  cnf(c_0_34, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.44  cnf(c_0_35, negated_conjecture, (k2_partfun1(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),u1_struct_0(X2))=k2_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),X2)|v2_struct_0(X1)|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_18]), c_0_19]), c_0_20])]), c_0_16])).
% 0.19/0.44  fof(c_0_36, plain, ![X7, X8]:(~v2_pre_topc(X7)|~l1_pre_topc(X7)|(~m1_pre_topc(X8,X7)|v2_pre_topc(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.19/0.44  fof(c_0_37, plain, ![X16, X17, X18, X19, X20]:(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)|(~m1_pre_topc(X18,X16)|(~m1_pre_topc(X19,X16)|(~v1_funct_1(X20)|~v1_funct_2(X20,u1_struct_0(X18),u1_struct_0(X17))|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X17))))|(~m1_pre_topc(X19,X18)|k3_tmap_1(X16,X17,X18,X19,X20)=k2_partfun1(u1_struct_0(X18),u1_struct_0(X17),X20,u1_struct_0(X19)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.19/0.44  fof(c_0_38, plain, ![X30, X31, X32]:(~v2_pre_topc(X30)|~l1_pre_topc(X30)|(~m1_pre_topc(X31,X30)|(~m1_pre_topc(X32,X31)|m1_pre_topc(X32,X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.19/0.44  cnf(c_0_39, negated_conjecture, (k2_partfun1(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),u1_struct_0(X2))=k2_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),X2)|v2_struct_0(X1)|~l1_struct_0(esk3_0)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_16]), c_0_24])])).
% 0.19/0.44  cnf(c_0_40, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_41, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.44  cnf(c_0_42, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_43, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.44  cnf(c_0_44, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.44  cnf(c_0_45, negated_conjecture, (k2_partfun1(u1_struct_0(X1),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),u1_struct_0(X2))=k2_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,X1),X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_16]), c_0_31])])).
% 0.19/0.44  cnf(c_0_46, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_47, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_40]), c_0_29])])).
% 0.19/0.44  cnf(c_0_48, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_29]), c_0_42])])).
% 0.19/0.44  cnf(c_0_49, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.44  cnf(c_0_50, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.44  cnf(c_0_51, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),u1_struct_0(esk5_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])]), c_0_49])).
% 0.19/0.44  cnf(c_0_52, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)|v2_struct_0(X1)|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_46]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.44  cnf(c_0_53, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,X1))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.44  cnf(c_0_54, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)|v2_struct_0(X1)|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)|~l1_struct_0(esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_23])).
% 0.19/0.44  cnf(c_0_55, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)|v2_struct_0(X1)|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~l1_struct_0(esk3_0)|~l1_struct_0(esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_16]), c_0_24])])).
% 0.19/0.45  cnf(c_0_56, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  cnf(c_0_57, negated_conjecture, (v2_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_28]), c_0_29]), c_0_42])])).
% 0.19/0.45  cnf(c_0_58, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)|v2_struct_0(X1)|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~l1_struct_0(esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_16]), c_0_31])])).
% 0.19/0.45  cnf(c_0_59, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1))=k2_tmap_1(esk3_0,esk2_0,esk6_0,X1)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_18]), c_0_19]), c_0_20]), c_0_24]), c_0_25])]), c_0_26]), c_0_56]), c_0_31]), c_0_57])])).
% 0.19/0.45  cnf(c_0_60, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)|v2_struct_0(X1)|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_16]), c_0_47])])).
% 0.19/0.45  fof(c_0_61, plain, ![X25, X26, X27, X28, X29]:(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25)|(v2_struct_0(X28)|~m1_pre_topc(X28,X25)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X25),u1_struct_0(X26))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))|(~m1_pre_topc(X27,X28)|r2_funct_2(u1_struct_0(X27),u1_struct_0(X26),k3_tmap_1(X25,X26,X28,X27,k2_tmap_1(X25,X26,X29,X28)),k2_tmap_1(X25,X26,X29,X27)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_tmap_1])])])])).
% 0.19/0.45  cnf(c_0_62, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,X2,esk6_0)=k2_tmap_1(esk3_0,esk2_0,esk6_0,X2)|v2_struct_0(X1)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_59]), c_0_18]), c_0_19]), c_0_20]), c_0_24]), c_0_25])]), c_0_26])).
% 0.19/0.45  cnf(c_0_63, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  cnf(c_0_64, negated_conjecture, (m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_44, c_0_46])).
% 0.19/0.45  cnf(c_0_65, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)|v2_struct_0(X1)|~l1_struct_0(esk4_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_15]), c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.45  cnf(c_0_66, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.45  cnf(c_0_67, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk6_0)=k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.45  cnf(c_0_68, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  cnf(c_0_69, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_57]), c_0_63]), c_0_31])])).
% 0.19/0.45  cnf(c_0_70, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)|v2_struct_0(X1)|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_16]), c_0_47])])).
% 0.19/0.45  cnf(c_0_71, plain, (r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,X4,X1,k2_tmap_1(X3,X2,X5,X4)),k2_tmap_1(X3,X2,X5,X1))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X4)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~v2_pre_topc(X3)), inference(csr,[status(thm)],[c_0_66, c_0_44])).
% 0.19/0.45  cnf(c_0_72, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  cnf(c_0_73, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)=k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_28]), c_0_29]), c_0_42])]), c_0_68])).
% 0.19/0.45  cnf(c_0_74, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,esk5_0,esk6_0)=k2_tmap_1(esk3_0,esk2_0,esk6_0,esk5_0)|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_62, c_0_69])).
% 0.19/0.45  cnf(c_0_75, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)|v2_struct_0(X1)|~l1_struct_0(esk3_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_16]), c_0_24])])).
% 0.19/0.45  cnf(c_0_76, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk3_0,esk2_0,X2,X1,k2_tmap_1(esk3_0,esk2_0,esk6_0,X2)),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(X1,X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_18]), c_0_19]), c_0_20]), c_0_24]), c_0_31]), c_0_25]), c_0_57])]), c_0_26]), c_0_56])).
% 0.19/0.45  cnf(c_0_77, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.45  cnf(c_0_78, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0)=k2_tmap_1(esk3_0,esk2_0,esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_28]), c_0_29]), c_0_42])]), c_0_68])).
% 0.19/0.45  cnf(c_0_79, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_16]), c_0_31])])).
% 0.19/0.45  cnf(c_0_80, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk3_0,esk2_0,esk4_0,X1,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1))|v2_struct_0(X1)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_63]), c_0_49])).
% 0.19/0.45  cnf(c_0_81, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  cnf(c_0_82, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)),k2_tmap_1(esk3_0,esk2_0,esk6_0,esk5_0))), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.45  cnf(c_0_83, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_40]), c_0_29]), c_0_42])]), c_0_68])).
% 0.19/0.45  cnf(c_0_84, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)),k2_tmap_1(esk3_0,esk2_0,esk6_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_46]), c_0_81])).
% 0.19/0.45  cnf(c_0_85, negated_conjecture, (k3_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_63]), c_0_31]), c_0_57])]), c_0_56])).
% 0.19/0.45  cnf(c_0_86, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0),esk5_0),k2_tmap_1(esk3_0,esk2_0,esk6_0,esk5_0))), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.45  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85]), c_0_86]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 88
% 0.19/0.45  # Proof object clause steps            : 69
% 0.19/0.45  # Proof object formula steps           : 19
% 0.19/0.45  # Proof object conjectures             : 59
% 0.19/0.45  # Proof object clause conjectures      : 56
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 27
% 0.19/0.45  # Proof object initial formulas used   : 9
% 0.19/0.45  # Proof object generating inferences   : 36
% 0.19/0.45  # Proof object simplifying inferences  : 119
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 9
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 28
% 0.19/0.45  # Removed in clause preprocessing      : 0
% 0.19/0.45  # Initial clauses in saturation        : 28
% 0.19/0.45  # Processed clauses                    : 501
% 0.19/0.45  # ...of these trivial                  : 4
% 0.19/0.45  # ...subsumed                          : 66
% 0.19/0.45  # ...remaining for further processing  : 430
% 0.19/0.45  # Other redundant clauses eliminated   : 0
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 67
% 0.19/0.45  # Backward-rewritten                   : 6
% 0.19/0.45  # Generated clauses                    : 675
% 0.19/0.45  # ...of the previous two non-trivial   : 535
% 0.19/0.45  # Contextual simplify-reflections      : 62
% 0.19/0.45  # Paramodulations                      : 675
% 0.19/0.45  # Factorizations                       : 0
% 0.19/0.45  # Equation resolutions                 : 0
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 329
% 0.19/0.45  #    Positive orientable unit clauses  : 33
% 0.19/0.45  #    Positive unorientable unit clauses: 0
% 0.19/0.45  #    Negative unit clauses             : 6
% 0.19/0.45  #    Non-unit-clauses                  : 290
% 0.19/0.45  # Current number of unprocessed clauses: 68
% 0.19/0.45  # ...number of literals in the above   : 635
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 101
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 24319
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 2939
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 195
% 0.19/0.45  # Unit Clause-clause subsumption calls : 10
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 55
% 0.19/0.45  # BW rewrite match successes           : 6
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 49124
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.106 s
% 0.19/0.45  # System time              : 0.005 s
% 0.19/0.45  # Total time               : 0.111 s
% 0.19/0.45  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
