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
% DateTime   : Thu Dec  3 11:18:08 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  140 (9128 expanded)
%              Number of clauses        :  117 (2846 expanded)
%              Number of leaves         :   11 (2229 expanded)
%              Depth                    :   16
%              Number of atoms          :  725 (150983 expanded)
%              Number of equality atoms :   41 ( 323 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   39 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t90_tmap_1,conjecture,(
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
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X5,X3) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                           => ( ( v1_funct_1(k3_tmap_1(X1,X2,X4,X3,X6))
                                & v1_funct_2(k3_tmap_1(X1,X2,X4,X3,X6),u1_struct_0(X3),u1_struct_0(X2))
                                & v5_pre_topc(k3_tmap_1(X1,X2,X4,X3,X6),X3,X2)
                                & m1_subset_1(k3_tmap_1(X1,X2,X4,X3,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                             => ( v1_funct_1(k3_tmap_1(X1,X2,X4,X5,X6))
                                & v1_funct_2(k3_tmap_1(X1,X2,X4,X5,X6),u1_struct_0(X5),u1_struct_0(X2))
                                & v5_pre_topc(k3_tmap_1(X1,X2,X4,X5,X6),X5,X2)
                                & m1_subset_1(k3_tmap_1(X1,X2,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(fc2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & v5_pre_topc(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & ~ v2_struct_0(X4)
        & m1_pre_topc(X4,X1) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tmap_1)).

fof(t79_tmap_1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(c_0_11,negated_conjecture,(
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
                       => ( ( m1_pre_topc(X3,X4)
                            & m1_pre_topc(X5,X3) )
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                             => ( ( v1_funct_1(k3_tmap_1(X1,X2,X4,X3,X6))
                                  & v1_funct_2(k3_tmap_1(X1,X2,X4,X3,X6),u1_struct_0(X3),u1_struct_0(X2))
                                  & v5_pre_topc(k3_tmap_1(X1,X2,X4,X3,X6),X3,X2)
                                  & m1_subset_1(k3_tmap_1(X1,X2,X4,X3,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                               => ( v1_funct_1(k3_tmap_1(X1,X2,X4,X5,X6))
                                  & v1_funct_2(k3_tmap_1(X1,X2,X4,X5,X6),u1_struct_0(X5),u1_struct_0(X2))
                                  & v5_pre_topc(k3_tmap_1(X1,X2,X4,X5,X6),X5,X2)
                                  & m1_subset_1(k3_tmap_1(X1,X2,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t90_tmap_1])).

fof(c_0_12,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( v1_funct_1(k3_tmap_1(X24,X25,X26,X27,X28))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_pre_topc(X26,X24)
        | ~ m1_pre_topc(X27,X24)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X25))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25)))) )
      & ( v1_funct_2(k3_tmap_1(X24,X25,X26,X27,X28),u1_struct_0(X27),u1_struct_0(X25))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_pre_topc(X26,X24)
        | ~ m1_pre_topc(X27,X24)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X25))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25)))) )
      & ( m1_subset_1(k3_tmap_1(X24,X25,X26,X27,X28),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X25))))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_pre_topc(X26,X24)
        | ~ m1_pre_topc(X27,X24)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X25))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

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
    & m1_pre_topc(esk3_0,esk4_0)
    & m1_pre_topc(esk5_0,esk3_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    & v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))
    & v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    & v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk3_0,esk2_0)
    & m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    & ( ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))
      | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0,esk2_0)
      | ~ m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_14,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | l1_pre_topc(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_22,plain,(
    ! [X11,X12] :
      ( ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(X12,X11)
      | v2_pre_topc(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_25,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | v2_struct_0(X20)
      | ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_pre_topc(X21,X19)
      | ~ m1_pre_topc(X22,X19)
      | ~ v1_funct_1(X23)
      | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))
      | ~ m1_pre_topc(X22,X21)
      | k3_tmap_1(X19,X20,X21,X22,X23) = k2_partfun1(u1_struct_0(X21),u1_struct_0(X20),X23,u1_struct_0(X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_26,plain,(
    ! [X40,X41,X42] :
      ( ~ v2_pre_topc(X40)
      | ~ l1_pre_topc(X40)
      | ~ m1_pre_topc(X41,X40)
      | ~ m1_pre_topc(X42,X41)
      | m1_pre_topc(X42,X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_27,plain,(
    ! [X15,X16,X17,X18] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | ~ v1_funct_1(X17)
      | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
      | ~ m1_pre_topc(X18,X15)
      | k2_tmap_1(X15,X16,X17,X18) = k2_partfun1(u1_struct_0(X15),u1_struct_0(X16),X17,u1_struct_0(X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_28,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(X1,esk2_0,esk4_0,X2,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(X1,esk2_0,esk4_0,X2,esk6_0),u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(X1,esk2_0,esk4_0,X2,esk6_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

fof(c_0_38,plain,(
    ! [X33] :
      ( ~ l1_pre_topc(X33)
      | m1_pre_topc(X33,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_39,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_29]),c_0_31])])).

cnf(c_0_44,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_29]),c_0_31]),c_0_32])])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_29]),c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_29]),c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_48,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5) ),
    inference(csr,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(X1)) = k2_tmap_1(esk5_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),X1)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_16]),c_0_43]),c_0_17]),c_0_44]),c_0_45]),c_0_46])]),c_0_20]),c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_49]),c_0_31])])).

cnf(c_0_56,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_49]),c_0_31]),c_0_32])])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_59,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_60,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_30]),c_0_31])])).

cnf(c_0_61,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_62,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_63,negated_conjecture,
    ( m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_65,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk5_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) = k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_42]),c_0_16]),c_0_17]),c_0_45]),c_0_46])]),c_0_20])).

cnf(c_0_66,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0)) = k2_tmap_1(esk5_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_67,plain,(
    ! [X29,X30,X31,X32] :
      ( ( v1_funct_1(k2_tmap_1(X29,X30,X31,X32))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))
        | ~ v5_pre_topc(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X29) )
      & ( v1_funct_2(k2_tmap_1(X29,X30,X31,X32),u1_struct_0(X32),u1_struct_0(X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))
        | ~ v5_pre_topc(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X29) )
      & ( v5_pre_topc(k2_tmap_1(X29,X30,X31,X32),X32,X30)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))
        | ~ v5_pre_topc(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tmap_1])])])])).

cnf(c_0_68,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_54]),c_0_16]),c_0_55]),c_0_17]),c_0_56]),c_0_57]),c_0_58])]),c_0_20]),c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1)) = k2_tmap_1(esk4_0,esk2_0,esk6_0,X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_15]),c_0_16]),c_0_60]),c_0_17]),c_0_61]),c_0_18]),c_0_19])]),c_0_20]),c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_60]),c_0_61])])).

cnf(c_0_71,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) = k2_tmap_1(esk5_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_53]),c_0_66])).

cnf(c_0_72,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_74,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_54]),c_0_16]),c_0_17]),c_0_57]),c_0_58])]),c_0_20])).

cnf(c_0_77,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),u1_struct_0(esk5_0)) = k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_50])).

fof(c_0_78,plain,(
    ! [X34,X35,X36,X37,X38,X39] :
      ( v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | v2_struct_0(X36)
      | ~ m1_pre_topc(X36,X34)
      | v2_struct_0(X37)
      | ~ m1_pre_topc(X37,X34)
      | v2_struct_0(X38)
      | ~ m1_pre_topc(X38,X34)
      | ~ m1_pre_topc(X37,X36)
      | ~ m1_pre_topc(X38,X37)
      | ~ v1_funct_1(X39)
      | ~ v1_funct_2(X39,u1_struct_0(X36),u1_struct_0(X35))
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))
      | r2_funct_2(u1_struct_0(X38),u1_struct_0(X35),k3_tmap_1(X34,X35,X37,X38,k3_tmap_1(X34,X35,X36,X37,X39)),k3_tmap_1(X34,X35,X36,X38,X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_tmap_1])])])])).

cnf(c_0_79,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,X2,esk6_0) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_80,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk3_0)) = k2_tmap_1(esk4_0,esk2_0,esk6_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_64])).

cnf(c_0_81,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk5_0)) = k2_tmap_1(esk4_0,esk2_0,esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_82,negated_conjecture,
    ( k2_tmap_1(esk5_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0) = k3_tmap_1(esk5_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_53]),c_0_43]),c_0_44])]),c_0_47])).

cnf(c_0_83,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),X1),X1,esk2_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_16]),c_0_55]),c_0_17]),c_0_56]),c_0_54]),c_0_57]),c_0_58])]),c_0_20]),c_0_59])).

cnf(c_0_84,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),X1))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_73]),c_0_16]),c_0_55]),c_0_17]),c_0_56]),c_0_54]),c_0_57]),c_0_58])]),c_0_20]),c_0_59])).

cnf(c_0_85,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_73]),c_0_16]),c_0_55]),c_0_17]),c_0_56]),c_0_54]),c_0_57]),c_0_58])]),c_0_20]),c_0_59])).

cnf(c_0_86,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)) = k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_50]),c_0_77])).

cnf(c_0_87,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X5,X4)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,esk6_0) = k2_tmap_1(esk4_0,esk2_0,esk6_0,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_64]),c_0_80])).

cnf(c_0_89,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_60])).

cnf(c_0_90,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,esk6_0) = k2_tmap_1(esk4_0,esk2_0,esk6_0,esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_70]),c_0_81])).

cnf(c_0_91,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) = k3_tmap_1(esk5_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_71,c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0),esk5_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_50]),c_0_47])).

cnf(c_0_93,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_50]),c_0_47])).

cnf(c_0_94,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_50]),c_0_47])).

cnf(c_0_95,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(X1,esk2_0,esk3_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_54]),c_0_16]),c_0_17]),c_0_57]),c_0_58])]),c_0_20])).

cnf(c_0_96,negated_conjecture,
    ( k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0) = k3_tmap_1(esk4_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_64]),c_0_60]),c_0_61])]),c_0_62])).

cnf(c_0_97,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6))
    | ~ m1_pre_topc(X5,X4)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X6) ),
    inference(csr,[status(thm)],[c_0_87,c_0_40])).

cnf(c_0_98,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk2_0,esk6_0,esk3_0) = k3_tmap_1(esk4_0,esk2_0,esk4_0,esk3_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_60]),c_0_61])]),c_0_62])).

cnf(c_0_99,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk2_0,esk6_0,esk5_0) = k3_tmap_1(esk4_0,esk2_0,esk4_0,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_89]),c_0_60]),c_0_61])]),c_0_62])).

cnf(c_0_100,negated_conjecture,
    ( k3_tmap_1(esk5_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) = k3_tmap_1(esk4_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_70]),c_0_60]),c_0_61])]),c_0_62])).

cnf(c_0_101,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0),X1),X1,esk2_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_92]),c_0_16]),c_0_43]),c_0_17]),c_0_44]),c_0_93])]),c_0_20]),c_0_47]),c_0_94])])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk4_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_70]),c_0_64]),c_0_60]),c_0_61])]),c_0_62])).

cnf(c_0_103,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)) = k3_tmap_1(esk4_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_86,c_0_96])).

cnf(c_0_104,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(esk2_0),k3_tmap_1(X1,esk2_0,X2,X3,k3_tmap_1(X1,esk2_0,esk4_0,X2,esk6_0)),k3_tmap_1(X1,esk2_0,esk4_0,X3,esk6_0))
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_62]),c_0_20])).

cnf(c_0_105,negated_conjecture,
    ( m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_70])).

cnf(c_0_106,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,esk6_0) = k3_tmap_1(esk4_0,esk2_0,esk4_0,esk3_0,esk6_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_88,c_0_98])).

cnf(c_0_107,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,esk6_0) = k3_tmap_1(esk4_0,esk2_0,esk4_0,esk5_0,esk6_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_90,c_0_99])).

cnf(c_0_108,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) = k3_tmap_1(esk4_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_91,c_0_100])).

cnf(c_0_109,negated_conjecture,
    ( ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_110,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk5_0,esk2_0,k3_tmap_1(esk4_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),X1),X1,esk2_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_96]),c_0_96]),c_0_102])])).

cnf(c_0_111,negated_conjecture,
    ( k3_tmap_1(esk4_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)) = k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_49]),c_0_31]),c_0_32])]),c_0_33])).

fof(c_0_112,plain,(
    ! [X7,X8,X9,X10] :
      ( ( ~ r2_funct_2(X7,X8,X9,X10)
        | X9 = X10
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( X9 != X10
        | r2_funct_2(X7,X8,X9,X10)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_113,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(X1,esk2_0,esk3_0,esk5_0,k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,esk6_0)),k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,esk6_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_50]),c_0_64])]),c_0_59]),c_0_47]),c_0_105])).

cnf(c_0_114,negated_conjecture,
    ( k3_tmap_1(esk4_0,esk2_0,esk4_0,esk3_0,esk6_0) = k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_115,negated_conjecture,
    ( k3_tmap_1(esk4_0,esk2_0,esk4_0,esk5_0,esk6_0) = k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_116,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(X1,esk2_0,esk3_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_54]),c_0_16]),c_0_17]),c_0_57]),c_0_58])]),c_0_20])).

cnf(c_0_117,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(X1,esk2_0,esk3_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_54]),c_0_16]),c_0_17]),c_0_57]),c_0_58])]),c_0_20])).

cnf(c_0_118,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(X1,esk2_0,esk5_0,esk5_0,k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,esk6_0)),k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,esk6_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_53]),c_0_70])]),c_0_47]),c_0_105])).

cnf(c_0_119,negated_conjecture,
    ( k3_tmap_1(esk4_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) = k3_tmap_1(esk1_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_29]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_120,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(X1,esk2_0,esk5_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_42]),c_0_16]),c_0_17]),c_0_45]),c_0_46])]),c_0_20])).

cnf(c_0_121,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(X1,esk2_0,esk5_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_42]),c_0_16]),c_0_17]),c_0_45]),c_0_46])]),c_0_20])).

cnf(c_0_122,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(X1,esk2_0,esk5_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_42]),c_0_16]),c_0_17]),c_0_45]),c_0_46])]),c_0_20])).

cnf(c_0_123,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_46])])).

cnf(c_0_124,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk5_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),X1),X1,esk2_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_125,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_126,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_89]),c_0_114]),c_0_111]),c_0_115]),c_0_60]),c_0_61])]),c_0_62])).

cnf(c_0_127,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_29]),c_0_49]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_128,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_29]),c_0_49]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_129,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_29]),c_0_49]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_130,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_89]),c_0_115]),c_0_119]),c_0_115]),c_0_60]),c_0_61])]),c_0_62])).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_29]),c_0_29]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_132,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_29]),c_0_29]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_133,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_29]),c_0_29]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_134,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_45])])).

cnf(c_0_135,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk5_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),esk5_0),esk5_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_53]),c_0_47])).

cnf(c_0_136,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)) = k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_42]),c_0_127]),c_0_45]),c_0_128]),c_0_46]),c_0_129])])).

cnf(c_0_137,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) = k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_130]),c_0_42]),c_0_131]),c_0_45]),c_0_132]),c_0_46]),c_0_133])])).

cnf(c_0_138,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_42])])).

cnf(c_0_139,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_136]),c_0_82]),c_0_100]),c_0_119]),c_0_137]),c_0_138]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.34  % Computer   : n014.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 20:22:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.39/0.59  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.39/0.59  # and selection function SelectCQIPrecWNTNp.
% 0.39/0.59  #
% 0.39/0.59  # Preprocessing time       : 0.041 s
% 0.39/0.59  # Presaturation interreduction done
% 0.39/0.59  
% 0.39/0.59  # Proof found!
% 0.39/0.59  # SZS status Theorem
% 0.39/0.59  # SZS output start CNFRefutation
% 0.39/0.59  fof(t90_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X3,X4)&m1_pre_topc(X5,X3))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((((v1_funct_1(k3_tmap_1(X1,X2,X4,X3,X6))&v1_funct_2(k3_tmap_1(X1,X2,X4,X3,X6),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,X4,X3,X6),X3,X2))&m1_subset_1(k3_tmap_1(X1,X2,X4,X3,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(((v1_funct_1(k3_tmap_1(X1,X2,X4,X5,X6))&v1_funct_2(k3_tmap_1(X1,X2,X4,X5,X6),u1_struct_0(X5),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,X4,X5,X6),X5,X2))&m1_subset_1(k3_tmap_1(X1,X2,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_tmap_1)).
% 0.39/0.59  fof(dt_k3_tmap_1, axiom, ![X1, X2, X3, X4, X5]:(((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&m1_pre_topc(X3,X1))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))&v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 0.39/0.59  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.39/0.59  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.39/0.59  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.39/0.59  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.39/0.59  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.39/0.59  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.39/0.59  fof(fc2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&~(v2_struct_0(X4)))&m1_pre_topc(X4,X1))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tmap_1)).
% 0.39/0.59  fof(t79_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X4,X3)&m1_pre_topc(X5,X4))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tmap_1)).
% 0.39/0.59  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.39/0.59  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X3,X4)&m1_pre_topc(X5,X3))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((((v1_funct_1(k3_tmap_1(X1,X2,X4,X3,X6))&v1_funct_2(k3_tmap_1(X1,X2,X4,X3,X6),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,X4,X3,X6),X3,X2))&m1_subset_1(k3_tmap_1(X1,X2,X4,X3,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(((v1_funct_1(k3_tmap_1(X1,X2,X4,X5,X6))&v1_funct_2(k3_tmap_1(X1,X2,X4,X5,X6),u1_struct_0(X5),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,X4,X5,X6),X5,X2))&m1_subset_1(k3_tmap_1(X1,X2,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))))))))))))), inference(assume_negation,[status(cth)],[t90_tmap_1])).
% 0.39/0.59  fof(c_0_12, plain, ![X24, X25, X26, X27, X28]:(((v1_funct_1(k3_tmap_1(X24,X25,X26,X27,X28))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_pre_topc(X26,X24)|~m1_pre_topc(X27,X24)|~v1_funct_1(X28)|~v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X25))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25))))))&(v1_funct_2(k3_tmap_1(X24,X25,X26,X27,X28),u1_struct_0(X27),u1_struct_0(X25))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_pre_topc(X26,X24)|~m1_pre_topc(X27,X24)|~v1_funct_1(X28)|~v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X25))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25)))))))&(m1_subset_1(k3_tmap_1(X24,X25,X26,X27,X28),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X25))))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_pre_topc(X26,X24)|~m1_pre_topc(X27,X24)|~v1_funct_1(X28)|~v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X25))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).
% 0.39/0.59  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&((m1_pre_topc(esk3_0,esk4_0)&m1_pre_topc(esk5_0,esk3_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&((((v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))&v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk3_0,esk2_0))&m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&(~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))|~v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0,esk2_0)|~m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.39/0.59  cnf(c_0_14, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.39/0.59  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_17, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_18, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  fof(c_0_21, plain, ![X13, X14]:(~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|l1_pre_topc(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.39/0.59  fof(c_0_22, plain, ![X11, X12]:(~v2_pre_topc(X11)|~l1_pre_topc(X11)|(~m1_pre_topc(X12,X11)|v2_pre_topc(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.39/0.59  cnf(c_0_23, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.39/0.59  cnf(c_0_24, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.39/0.59  fof(c_0_25, plain, ![X19, X20, X21, X22, X23]:(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|(~m1_pre_topc(X21,X19)|(~m1_pre_topc(X22,X19)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))|(~m1_pre_topc(X22,X21)|k3_tmap_1(X19,X20,X21,X22,X23)=k2_partfun1(u1_struct_0(X21),u1_struct_0(X20),X23,u1_struct_0(X22)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.39/0.59  fof(c_0_26, plain, ![X40, X41, X42]:(~v2_pre_topc(X40)|~l1_pre_topc(X40)|(~m1_pre_topc(X41,X40)|(~m1_pre_topc(X42,X41)|m1_pre_topc(X42,X40)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.39/0.59  fof(c_0_27, plain, ![X15, X16, X17, X18]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))|(~m1_pre_topc(X18,X15)|k2_tmap_1(X15,X16,X17,X18)=k2_partfun1(u1_struct_0(X15),u1_struct_0(X16),X17,u1_struct_0(X18)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.39/0.59  cnf(c_0_28, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(X1,esk2_0,esk4_0,X2,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.39/0.59  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_30, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_34, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.39/0.59  cnf(c_0_35, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.39/0.59  cnf(c_0_36, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(X1,esk2_0,esk4_0,X2,esk6_0),u1_struct_0(X2),u1_struct_0(esk2_0))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.39/0.59  cnf(c_0_37, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(X1,esk2_0,esk4_0,X2,esk6_0))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.39/0.59  fof(c_0_38, plain, ![X33]:(~l1_pre_topc(X33)|m1_pre_topc(X33,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.39/0.59  cnf(c_0_39, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.39/0.59  cnf(c_0_40, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.59  cnf(c_0_41, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.39/0.59  cnf(c_0_42, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_32])]), c_0_33])).
% 0.39/0.59  cnf(c_0_43, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_29]), c_0_31])])).
% 0.39/0.59  cnf(c_0_44, negated_conjecture, (v2_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_29]), c_0_31]), c_0_32])])).
% 0.39/0.59  cnf(c_0_45, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_29]), c_0_30]), c_0_31]), c_0_32])]), c_0_33])).
% 0.39/0.59  cnf(c_0_46, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_29]), c_0_30]), c_0_31]), c_0_32])]), c_0_33])).
% 0.39/0.59  cnf(c_0_47, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_48, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.39/0.59  cnf(c_0_49, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_50, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_51, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)), inference(csr,[status(thm)],[c_0_39, c_0_40])).
% 0.39/0.59  cnf(c_0_52, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(X1))=k2_tmap_1(esk5_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),X1)|~m1_pre_topc(X1,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_16]), c_0_43]), c_0_17]), c_0_44]), c_0_45]), c_0_46])]), c_0_20]), c_0_47])).
% 0.39/0.59  cnf(c_0_53, negated_conjecture, (m1_pre_topc(esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_48, c_0_43])).
% 0.39/0.59  cnf(c_0_54, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_55, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_49]), c_0_31])])).
% 0.39/0.59  cnf(c_0_56, negated_conjecture, (v2_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_49]), c_0_31]), c_0_32])])).
% 0.39/0.59  cnf(c_0_57, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_58, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_59, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_60, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_30]), c_0_31])])).
% 0.39/0.59  cnf(c_0_61, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_30]), c_0_31]), c_0_32])])).
% 0.39/0.59  cnf(c_0_62, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_63, negated_conjecture, (m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_40, c_0_50])).
% 0.39/0.59  cnf(c_0_64, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_65, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk5_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))=k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk5_0)|~m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_42]), c_0_16]), c_0_17]), c_0_45]), c_0_46])]), c_0_20])).
% 0.39/0.59  cnf(c_0_66, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0))=k2_tmap_1(esk5_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.39/0.59  fof(c_0_67, plain, ![X29, X30, X31, X32]:(((v1_funct_1(k2_tmap_1(X29,X30,X31,X32))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))|~v5_pre_topc(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))|v2_struct_0(X32)|~m1_pre_topc(X32,X29)))&(v1_funct_2(k2_tmap_1(X29,X30,X31,X32),u1_struct_0(X32),u1_struct_0(X30))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))|~v5_pre_topc(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))|v2_struct_0(X32)|~m1_pre_topc(X32,X29))))&(v5_pre_topc(k2_tmap_1(X29,X30,X31,X32),X32,X30)|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))|~v5_pre_topc(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))|v2_struct_0(X32)|~m1_pre_topc(X32,X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tmap_1])])])])).
% 0.39/0.59  cnf(c_0_68, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),u1_struct_0(X1))=k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_54]), c_0_16]), c_0_55]), c_0_17]), c_0_56]), c_0_57]), c_0_58])]), c_0_20]), c_0_59])).
% 0.39/0.59  cnf(c_0_69, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1))=k2_tmap_1(esk4_0,esk2_0,esk6_0,X1)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_15]), c_0_16]), c_0_60]), c_0_17]), c_0_61]), c_0_18]), c_0_19])]), c_0_20]), c_0_62])).
% 0.39/0.59  cnf(c_0_70, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_60]), c_0_61])])).
% 0.39/0.59  cnf(c_0_71, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))=k2_tmap_1(esk5_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0)|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_53]), c_0_66])).
% 0.39/0.59  cnf(c_0_72, plain, (v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v5_pre_topc(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.39/0.59  cnf(c_0_73, negated_conjecture, (v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.59  cnf(c_0_74, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v5_pre_topc(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.39/0.59  cnf(c_0_75, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v5_pre_topc(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.39/0.60  cnf(c_0_76, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_54]), c_0_16]), c_0_17]), c_0_57]), c_0_58])]), c_0_20])).
% 0.39/0.60  cnf(c_0_77, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),u1_struct_0(esk5_0))=k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_68, c_0_50])).
% 0.39/0.60  fof(c_0_78, plain, ![X34, X35, X36, X37, X38, X39]:(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|(v2_struct_0(X36)|~m1_pre_topc(X36,X34)|(v2_struct_0(X37)|~m1_pre_topc(X37,X34)|(v2_struct_0(X38)|~m1_pre_topc(X38,X34)|(~m1_pre_topc(X37,X36)|~m1_pre_topc(X38,X37)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X36),u1_struct_0(X35))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))|r2_funct_2(u1_struct_0(X38),u1_struct_0(X35),k3_tmap_1(X34,X35,X37,X38,k3_tmap_1(X34,X35,X36,X37,X39)),k3_tmap_1(X34,X35,X36,X38,X39))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_tmap_1])])])])).
% 0.39/0.60  cnf(c_0_79, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,X2,esk6_0)=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.39/0.60  cnf(c_0_80, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk3_0))=k2_tmap_1(esk4_0,esk2_0,esk6_0,esk3_0)), inference(spm,[status(thm)],[c_0_69, c_0_64])).
% 0.39/0.60  cnf(c_0_81, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk5_0))=k2_tmap_1(esk4_0,esk2_0,esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.39/0.60  cnf(c_0_82, negated_conjecture, (k2_tmap_1(esk5_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0)=k3_tmap_1(esk5_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_53]), c_0_43]), c_0_44])]), c_0_47])).
% 0.39/0.60  cnf(c_0_83, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),X1),X1,esk2_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_16]), c_0_55]), c_0_17]), c_0_56]), c_0_54]), c_0_57]), c_0_58])]), c_0_20]), c_0_59])).
% 0.39/0.60  cnf(c_0_84, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),X1))|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_73]), c_0_16]), c_0_55]), c_0_17]), c_0_56]), c_0_54]), c_0_57]), c_0_58])]), c_0_20]), c_0_59])).
% 0.39/0.60  cnf(c_0_85, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_73]), c_0_16]), c_0_55]), c_0_17]), c_0_56]), c_0_54]), c_0_57]), c_0_58])]), c_0_20]), c_0_59])).
% 0.39/0.60  cnf(c_0_86, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))=k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0)|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_50]), c_0_77])).
% 0.39/0.60  cnf(c_0_87, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|v2_struct_0(X5)|r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X5,X1)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X5,X4)|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.39/0.60  cnf(c_0_88, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,esk6_0)=k2_tmap_1(esk4_0,esk2_0,esk6_0,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_64]), c_0_80])).
% 0.39/0.60  cnf(c_0_89, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_48, c_0_60])).
% 0.39/0.60  cnf(c_0_90, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,esk6_0)=k2_tmap_1(esk4_0,esk2_0,esk6_0,esk5_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_70]), c_0_81])).
% 0.39/0.60  cnf(c_0_91, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))=k3_tmap_1(esk5_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[c_0_71, c_0_82])).
% 0.39/0.60  cnf(c_0_92, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0),esk5_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_50]), c_0_47])).
% 0.39/0.60  cnf(c_0_93, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_50]), c_0_47])).
% 0.39/0.60  cnf(c_0_94, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_50]), c_0_47])).
% 0.39/0.60  cnf(c_0_95, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(X1,esk2_0,esk3_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_54]), c_0_16]), c_0_17]), c_0_57]), c_0_58])]), c_0_20])).
% 0.39/0.60  cnf(c_0_96, negated_conjecture, (k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0)=k3_tmap_1(esk4_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_64]), c_0_60]), c_0_61])]), c_0_62])).
% 0.39/0.60  cnf(c_0_97, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|v2_struct_0(X5)|r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6))|~m1_pre_topc(X5,X4)|~m1_pre_topc(X5,X1)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X6)), inference(csr,[status(thm)],[c_0_87, c_0_40])).
% 0.39/0.60  cnf(c_0_98, negated_conjecture, (k2_tmap_1(esk4_0,esk2_0,esk6_0,esk3_0)=k3_tmap_1(esk4_0,esk2_0,esk4_0,esk3_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_60]), c_0_61])]), c_0_62])).
% 0.39/0.60  cnf(c_0_99, negated_conjecture, (k2_tmap_1(esk4_0,esk2_0,esk6_0,esk5_0)=k3_tmap_1(esk4_0,esk2_0,esk4_0,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_89]), c_0_60]), c_0_61])]), c_0_62])).
% 0.39/0.60  cnf(c_0_100, negated_conjecture, (k3_tmap_1(esk5_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))=k3_tmap_1(esk4_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_70]), c_0_60]), c_0_61])]), c_0_62])).
% 0.39/0.60  cnf(c_0_101, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0),X1),X1,esk2_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_92]), c_0_16]), c_0_43]), c_0_17]), c_0_44]), c_0_93])]), c_0_20]), c_0_47]), c_0_94])])).
% 0.39/0.60  cnf(c_0_102, negated_conjecture, (m1_subset_1(k3_tmap_1(esk4_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_70]), c_0_64]), c_0_60]), c_0_61])]), c_0_62])).
% 0.39/0.60  cnf(c_0_103, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))=k3_tmap_1(esk4_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[c_0_86, c_0_96])).
% 0.39/0.60  cnf(c_0_104, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r2_funct_2(u1_struct_0(X3),u1_struct_0(esk2_0),k3_tmap_1(X1,esk2_0,X2,X3,k3_tmap_1(X1,esk2_0,esk4_0,X2,esk6_0)),k3_tmap_1(X1,esk2_0,esk4_0,X3,esk6_0))|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_62]), c_0_20])).
% 0.39/0.60  cnf(c_0_105, negated_conjecture, (m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_40, c_0_70])).
% 0.39/0.60  cnf(c_0_106, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,esk6_0)=k3_tmap_1(esk4_0,esk2_0,esk4_0,esk3_0,esk6_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[c_0_88, c_0_98])).
% 0.39/0.60  cnf(c_0_107, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,esk6_0)=k3_tmap_1(esk4_0,esk2_0,esk4_0,esk5_0,esk6_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[c_0_90, c_0_99])).
% 0.39/0.60  cnf(c_0_108, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))=k3_tmap_1(esk4_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[c_0_91, c_0_100])).
% 0.39/0.60  cnf(c_0_109, negated_conjecture, (~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))|~v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0,esk2_0)|~m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.60  cnf(c_0_110, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk5_0,esk2_0,k3_tmap_1(esk4_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),X1),X1,esk2_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_96]), c_0_96]), c_0_102])])).
% 0.39/0.60  cnf(c_0_111, negated_conjecture, (k3_tmap_1(esk4_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))=k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_49]), c_0_31]), c_0_32])]), c_0_33])).
% 0.39/0.60  fof(c_0_112, plain, ![X7, X8, X9, X10]:((~r2_funct_2(X7,X8,X9,X10)|X9=X10|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&(X9!=X10|r2_funct_2(X7,X8,X9,X10)|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.39/0.60  cnf(c_0_113, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(X1,esk2_0,esk3_0,esk5_0,k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,esk6_0)),k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,esk6_0))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_50]), c_0_64])]), c_0_59]), c_0_47]), c_0_105])).
% 0.39/0.60  cnf(c_0_114, negated_conjecture, (k3_tmap_1(esk4_0,esk2_0,esk4_0,esk3_0,esk6_0)=k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_30]), c_0_31]), c_0_32])]), c_0_33])).
% 0.39/0.60  cnf(c_0_115, negated_conjecture, (k3_tmap_1(esk4_0,esk2_0,esk4_0,esk5_0,esk6_0)=k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_30]), c_0_31]), c_0_32])]), c_0_33])).
% 0.39/0.60  cnf(c_0_116, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(X1,esk2_0,esk3_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),u1_struct_0(X2),u1_struct_0(esk2_0))|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_54]), c_0_16]), c_0_17]), c_0_57]), c_0_58])]), c_0_20])).
% 0.39/0.60  cnf(c_0_117, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(X1,esk2_0,esk3_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)))|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_54]), c_0_16]), c_0_17]), c_0_57]), c_0_58])]), c_0_20])).
% 0.39/0.60  cnf(c_0_118, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(X1,esk2_0,esk5_0,esk5_0,k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,esk6_0)),k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,esk6_0))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_53]), c_0_70])]), c_0_47]), c_0_105])).
% 0.39/0.60  cnf(c_0_119, negated_conjecture, (k3_tmap_1(esk4_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))=k3_tmap_1(esk1_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_29]), c_0_31]), c_0_32])]), c_0_33])).
% 0.39/0.60  cnf(c_0_120, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(X1,esk2_0,esk5_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_42]), c_0_16]), c_0_17]), c_0_45]), c_0_46])]), c_0_20])).
% 0.39/0.60  cnf(c_0_121, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(X1,esk2_0,esk5_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(X2),u1_struct_0(esk2_0))|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_42]), c_0_16]), c_0_17]), c_0_45]), c_0_46])]), c_0_20])).
% 0.39/0.60  cnf(c_0_122, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(X1,esk2_0,esk5_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)))|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_42]), c_0_16]), c_0_17]), c_0_45]), c_0_46])]), c_0_20])).
% 0.39/0.60  cnf(c_0_123, negated_conjecture, (~v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0,esk2_0)|~m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|~v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_46])])).
% 0.39/0.60  cnf(c_0_124, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk5_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),X1),X1,esk2_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk5_0)), inference(rw,[status(thm)],[c_0_110, c_0_111])).
% 0.39/0.60  cnf(c_0_125, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_112])).
% 0.39/0.60  cnf(c_0_126, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_89]), c_0_114]), c_0_111]), c_0_115]), c_0_60]), c_0_61])]), c_0_62])).
% 0.39/0.60  cnf(c_0_127, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_29]), c_0_49]), c_0_31]), c_0_32])]), c_0_33])).
% 0.39/0.60  cnf(c_0_128, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_29]), c_0_49]), c_0_31]), c_0_32])]), c_0_33])).
% 0.39/0.60  cnf(c_0_129, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_29]), c_0_49]), c_0_31]), c_0_32])]), c_0_33])).
% 0.39/0.60  cnf(c_0_130, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_89]), c_0_115]), c_0_119]), c_0_115]), c_0_60]), c_0_61])]), c_0_62])).
% 0.39/0.60  cnf(c_0_131, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_29]), c_0_29]), c_0_31]), c_0_32])]), c_0_33])).
% 0.39/0.60  cnf(c_0_132, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_29]), c_0_29]), c_0_31]), c_0_32])]), c_0_33])).
% 0.39/0.60  cnf(c_0_133, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_29]), c_0_29]), c_0_31]), c_0_32])]), c_0_33])).
% 0.39/0.60  cnf(c_0_134, negated_conjecture, (~v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0,esk2_0)|~m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_45])])).
% 0.39/0.60  cnf(c_0_135, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk5_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),esk5_0),esk5_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_53]), c_0_47])).
% 0.39/0.60  cnf(c_0_136, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))=k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_42]), c_0_127]), c_0_45]), c_0_128]), c_0_46]), c_0_129])])).
% 0.39/0.60  cnf(c_0_137, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk5_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))=k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_130]), c_0_42]), c_0_131]), c_0_45]), c_0_132]), c_0_46]), c_0_133])])).
% 0.39/0.60  cnf(c_0_138, negated_conjecture, (~v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134, c_0_42])])).
% 0.39/0.60  cnf(c_0_139, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_136]), c_0_82]), c_0_100]), c_0_119]), c_0_137]), c_0_138]), ['proof']).
% 0.39/0.60  # SZS output end CNFRefutation
% 0.39/0.60  # Proof object total steps             : 140
% 0.39/0.60  # Proof object clause steps            : 117
% 0.39/0.60  # Proof object formula steps           : 23
% 0.39/0.60  # Proof object conjectures             : 104
% 0.39/0.60  # Proof object clause conjectures      : 101
% 0.39/0.60  # Proof object formula conjectures     : 3
% 0.39/0.60  # Proof object initial clauses used    : 36
% 0.39/0.60  # Proof object initial formulas used   : 11
% 0.39/0.60  # Proof object generating inferences   : 68
% 0.39/0.60  # Proof object simplifying inferences  : 319
% 0.39/0.60  # Training examples: 0 positive, 0 negative
% 0.39/0.60  # Parsed axioms                        : 11
% 0.39/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.60  # Initial clauses                      : 37
% 0.39/0.60  # Removed in clause preprocessing      : 0
% 0.39/0.60  # Initial clauses in saturation        : 37
% 0.39/0.60  # Processed clauses                    : 1594
% 0.39/0.60  # ...of these trivial                  : 21
% 0.39/0.60  # ...subsumed                          : 130
% 0.39/0.60  # ...remaining for further processing  : 1443
% 0.39/0.60  # Other redundant clauses eliminated   : 1
% 0.39/0.60  # Clauses deleted for lack of memory   : 0
% 0.39/0.60  # Backward-subsumed                    : 0
% 0.39/0.60  # Backward-rewritten                   : 618
% 0.39/0.60  # Generated clauses                    : 2000
% 0.39/0.60  # ...of the previous two non-trivial   : 2188
% 0.39/0.60  # Contextual simplify-reflections      : 19
% 0.39/0.60  # Paramodulations                      : 1999
% 0.39/0.60  # Factorizations                       : 0
% 0.39/0.60  # Equation resolutions                 : 1
% 0.39/0.60  # Propositional unsat checks           : 0
% 0.39/0.60  #    Propositional check models        : 0
% 0.39/0.60  #    Propositional check unsatisfiable : 0
% 0.39/0.60  #    Propositional clauses             : 0
% 0.39/0.60  #    Propositional clauses after purity: 0
% 0.39/0.60  #    Propositional unsat core size     : 0
% 0.39/0.60  #    Propositional preprocessing time  : 0.000
% 0.39/0.60  #    Propositional encoding time       : 0.000
% 0.39/0.60  #    Propositional solver time         : 0.000
% 0.39/0.60  #    Success case prop preproc time    : 0.000
% 0.39/0.60  #    Success case prop encoding time   : 0.000
% 0.39/0.60  #    Success case prop solver time     : 0.000
% 0.39/0.60  # Current number of processed clauses  : 787
% 0.39/0.60  #    Positive orientable unit clauses  : 370
% 0.39/0.60  #    Positive unorientable unit clauses: 0
% 0.39/0.60  #    Negative unit clauses             : 6
% 0.39/0.60  #    Non-unit-clauses                  : 411
% 0.39/0.60  # Current number of unprocessed clauses: 554
% 0.39/0.60  # ...number of literals in the above   : 1791
% 0.39/0.60  # Current number of archived formulas  : 0
% 0.39/0.60  # Current number of archived clauses   : 655
% 0.39/0.60  # Clause-clause subsumption calls (NU) : 38189
% 0.39/0.60  # Rec. Clause-clause subsumption calls : 5223
% 0.39/0.60  # Non-unit clause-clause subsumptions  : 149
% 0.39/0.60  # Unit Clause-clause subsumption calls : 53424
% 0.39/0.60  # Rewrite failures with RHS unbound    : 0
% 0.39/0.60  # BW rewrite match attempts            : 24576
% 0.39/0.60  # BW rewrite match successes           : 33
% 0.39/0.60  # Condensation attempts                : 0
% 0.39/0.60  # Condensation successes               : 0
% 0.39/0.60  # Termbank termtop insertions          : 107233
% 0.39/0.60  
% 0.39/0.60  # -------------------------------------------------
% 0.39/0.60  # User time                : 0.245 s
% 0.39/0.60  # System time              : 0.005 s
% 0.39/0.60  # Total time               : 0.249 s
% 0.39/0.60  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
