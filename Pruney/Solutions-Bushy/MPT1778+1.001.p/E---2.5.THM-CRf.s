%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1778+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:43 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 (2127 expanded)
%              Number of clauses        :   55 ( 633 expanded)
%              Number of leaves         :    7 ( 517 expanded)
%              Depth                    :   17
%              Number of atoms          :  463 (29741 expanded)
%              Number of equality atoms :    8 (  17 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t89_tmap_1,conjecture,(
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
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & v5_pre_topc(X5,X3,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
                          & v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
                          & v5_pre_topc(k3_tmap_1(X1,X2,X3,X4,X5),X4,X2)
                          & m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_tmap_1)).

fof(dt_k3_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_pre_topc(X3,X1)
        & m1_pre_topc(X4,X1)
        & v1_funct_1(X5)
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
     => ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
        & v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

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

fof(t49_tmap_1,axiom,(
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
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ( v5_pre_topc(X3,X2,X1)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => r1_tmap_1(X2,X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

fof(t15_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( m1_pre_topc(X2,X3)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => ? [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X3))
                        & X5 = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tmap_1)).

fof(t81_tmap_1,axiom,(
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
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X3))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X4))
                             => ( ( X6 = X7
                                  & m1_pre_topc(X4,X3)
                                  & r1_tmap_1(X3,X2,X5,X6) )
                               => r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

fof(c_0_7,negated_conjecture,(
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
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                          & v5_pre_topc(X5,X3,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                       => ( m1_pre_topc(X4,X3)
                         => ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
                            & v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(k3_tmap_1(X1,X2,X3,X4,X5),X4,X2)
                            & m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t89_tmap_1])).

fof(c_0_8,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( v1_funct_1(k3_tmap_1(X10,X11,X12,X13,X14))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | ~ m1_pre_topc(X12,X10)
        | ~ m1_pre_topc(X13,X10)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X11))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X11)))) )
      & ( v1_funct_2(k3_tmap_1(X10,X11,X12,X13,X14),u1_struct_0(X13),u1_struct_0(X11))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | ~ m1_pre_topc(X12,X10)
        | ~ m1_pre_topc(X13,X10)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X11))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X11)))) )
      & ( m1_subset_1(k3_tmap_1(X10,X11,X12,X13,X14),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X11))))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | ~ m1_pre_topc(X12,X10)
        | ~ m1_pre_topc(X13,X10)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X11))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X11)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk3_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk3_0)
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    & v5_pre_topc(esk7_0,esk5_0,esk4_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))
    & m1_pre_topc(esk6_0,esk5_0)
    & ( ~ v1_funct_1(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))
      | ~ v1_funct_2(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),u1_struct_0(esk6_0),u1_struct_0(esk4_0))
      | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk6_0,esk4_0)
      | ~ m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_10,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(X1,esk4_0,esk5_0,X2,esk7_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_24,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_25,plain,(
    ! [X8,X9] :
      ( ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | v2_pre_topc(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_funct_1(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),u1_struct_0(esk6_0),u1_struct_0(esk4_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk6_0,esk4_0)
    | ~ m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(X1,esk4_0,esk5_0,X2,esk7_0),u1_struct_0(X2),u1_struct_0(esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

fof(c_0_29,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ v5_pre_topc(X24,X23,X22)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | r1_tmap_1(X23,X22,X24,X25)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22))))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk2_3(X22,X23,X24),u1_struct_0(X23))
        | v5_pre_topc(X24,X23,X22)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22))))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ r1_tmap_1(X23,X22,X24,esk2_3(X22,X23,X24))
        | v5_pre_topc(X24,X23,X22)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22))))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

cnf(c_0_30,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk6_0,esk4_0)
    | ~ m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0))))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),u1_struct_0(esk6_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),u1_struct_0(esk6_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_34,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X2))
    | v5_pre_topc(X3,X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_18]),c_0_20])])).

cnf(c_0_37,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_18]),c_0_20]),c_0_21])])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk6_0,esk4_0)
    | ~ m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(X1,esk4_0,esk5_0,X2,esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk4_0))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

fof(c_0_41,plain,(
    ! [X17,X18,X19,X20] :
      ( ( m1_subset_1(esk1_4(X17,X18,X19,X20),u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_pre_topc(X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( esk1_4(X17,X18,X19,X20) = X20
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | ~ m1_pre_topc(X18,X19)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_tmap_1])])])])])])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk6_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0))
    | ~ m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_27]),c_0_36]),c_0_14]),c_0_37]),c_0_15])]),c_0_38]),c_0_16]),c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk6_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_46,plain,
    ( r1_tmap_1(X2,X3,X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( v5_pre_topc(esk7_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_48,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_19]),c_0_20])])).

cnf(c_0_49,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk1_4(X1,esk6_0,X2,esk2_3(esk4_0,esk6_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk6_0,X2)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_53,plain,
    ( esk1_4(X1,X2,X3,X4) = X4
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_54,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33] :
      ( v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | v2_struct_0(X29)
      | ~ m1_pre_topc(X29,X27)
      | v2_struct_0(X30)
      | ~ m1_pre_topc(X30,X27)
      | ~ v1_funct_1(X31)
      | ~ v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X28))
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X28))))
      | ~ m1_subset_1(X32,u1_struct_0(X29))
      | ~ m1_subset_1(X33,u1_struct_0(X30))
      | X32 != X33
      | ~ m1_pre_topc(X30,X29)
      | ~ r1_tmap_1(X29,X28,X31,X32)
      | r1_tmap_1(X30,X28,k3_tmap_1(X27,X28,X29,X30,X31),X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t81_tmap_1])])])])).

cnf(c_0_55,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_12]),c_0_11]),c_0_13]),c_0_14]),c_0_48]),c_0_15]),c_0_49])]),c_0_16]),c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk1_4(esk3_0,esk6_0,esk5_0,esk2_3(esk4_0,esk6_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_19]),c_0_52]),c_0_18]),c_0_20]),c_0_21])]),c_0_22]),c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( esk1_4(X1,esk6_0,X2,esk2_3(esk4_0,esk6_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))) = esk2_3(esk4_0,esk6_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(esk6_0,X2)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_45]),c_0_38])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | X6 != X7
    | ~ m1_pre_topc(X4,X3)
    | ~ r1_tmap_1(X3,X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,esk7_0,esk1_4(esk3_0,esk6_0,esk5_0,esk2_3(esk4_0,esk6_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( esk1_4(esk3_0,esk6_0,esk5_0,esk2_3(esk4_0,esk6_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))) = esk2_3(esk4_0,esk6_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_19]),c_0_52]),c_0_18]),c_0_20]),c_0_21])]),c_0_22]),c_0_50])).

cnf(c_0_61,plain,
    ( r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X4,X2,X5,X6)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,esk7_0,esk2_3(esk4_0,esk6_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk6_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)),u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r1_tmap_1(X1,esk4_0,k3_tmap_1(X2,esk4_0,esk5_0,X1,esk7_0),esk2_3(esk4_0,esk6_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(esk2_3(esk4_0,esk6_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_12]),c_0_63]),c_0_11]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk4_0,k3_tmap_1(X1,esk4_0,esk5_0,esk6_0,esk7_0),esk2_3(esk4_0,esk6_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_45]),c_0_52])]),c_0_38])).

cnf(c_0_66,plain,
    ( v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,X3,esk2_3(X2,X1,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_67,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk4_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk2_3(esk4_0,esk6_0,k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_19]),c_0_18]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_68,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_43])])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_43]),c_0_33]),c_0_27]),c_0_14]),c_0_36]),c_0_15]),c_0_37])]),c_0_68]),c_0_16]),c_0_38]),
    [proof]).

%------------------------------------------------------------------------------
