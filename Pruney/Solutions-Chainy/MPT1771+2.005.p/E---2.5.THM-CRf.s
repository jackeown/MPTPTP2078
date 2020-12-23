%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:45 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   92 (1240 expanded)
%              Number of clauses        :   73 ( 387 expanded)
%              Number of leaves         :    9 ( 300 expanded)
%              Depth                    :   12
%              Number of atoms          :  604 (16582 expanded)
%              Number of equality atoms :   30 ( 795 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal clause size      :   36 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t82_tmap_1,conjecture,(
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
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( ( X6 = X7
                                    & r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X5,X4),X6) )
                                 => r1_tmap_1(X3,X2,k2_tmap_1(X1,X2,X5,X3),X7) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tmap_1)).

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

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X33,X34,X35] :
      ( ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ m1_pre_topc(X34,X33)
      | ~ m1_pre_topc(X35,X34)
      | m1_pre_topc(X35,X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

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
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ( m1_pre_topc(X3,X4)
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X4))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X3))
                                 => ( ( X6 = X7
                                      & r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X5,X4),X6) )
                                   => r1_tmap_1(X3,X2,k2_tmap_1(X1,X2,X5,X3),X7) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t82_tmap_1])).

fof(c_0_12,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
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
      | v2_struct_0(X31)
      | ~ m1_pre_topc(X31,X27)
      | ~ m1_pre_topc(X30,X29)
      | ~ m1_pre_topc(X31,X30)
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,u1_struct_0(X29),u1_struct_0(X28))
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X28))))
      | r2_funct_2(u1_struct_0(X31),u1_struct_0(X28),k3_tmap_1(X27,X28,X30,X31,k3_tmap_1(X27,X28,X29,X30,X32)),k3_tmap_1(X27,X28,X29,X31,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_tmap_1])])])])).

cnf(c_0_13,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,negated_conjecture,
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
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & m1_pre_topc(esk3_0,esk4_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk3_0))
    & esk6_0 = esk7_0
    & r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk6_0)
    & ~ r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_16,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( v1_funct_1(k3_tmap_1(X21,X22,X23,X24,X25))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_pre_topc(X23,X21)
        | ~ m1_pre_topc(X24,X21)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22)))) )
      & ( v1_funct_2(k3_tmap_1(X21,X22,X23,X24,X25),u1_struct_0(X24),u1_struct_0(X22))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_pre_topc(X23,X21)
        | ~ m1_pre_topc(X24,X21)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22)))) )
      & ( m1_subset_1(k3_tmap_1(X21,X22,X23,X24,X25),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X22))))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_pre_topc(X23,X21)
        | ~ m1_pre_topc(X24,X21)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

fof(c_0_18,plain,(
    ! [X26] :
      ( ~ l1_pre_topc(X26)
      | m1_pre_topc(X26,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_19,plain,
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
    inference(csr,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
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
    inference(csr,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(esk2_0),k3_tmap_1(X1,esk2_0,X2,X3,k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0)),k3_tmap_1(X1,esk2_0,esk1_0,X3,esk5_0))
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_27]),c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0))
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0),u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

fof(c_0_42,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | v2_struct_0(X37)
      | ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | v2_struct_0(X38)
      | ~ m1_pre_topc(X38,X36)
      | v2_struct_0(X39)
      | ~ m1_pre_topc(X39,X36)
      | ~ v1_funct_1(X40)
      | ~ v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X37))
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X37))))
      | ~ m1_subset_1(X41,u1_struct_0(X38))
      | ~ m1_subset_1(X42,u1_struct_0(X39))
      | X41 != X42
      | ~ m1_pre_topc(X39,X38)
      | ~ r1_tmap_1(X38,X37,X40,X41)
      | r1_tmap_1(X39,X37,k3_tmap_1(X36,X37,X38,X39,X40),X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t81_tmap_1])])])])).

fof(c_0_43,plain,(
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

cnf(c_0_44,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,esk4_0,esk5_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_45,plain,(
    ! [X8,X9,X10,X11] :
      ( ( ~ r2_funct_2(X8,X9,X10,X11)
        | X10 = X11
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X8,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( X10 != X11
        | r2_funct_2(X8,X9,X10,X11)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X8,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_46,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(X2,esk2_0,esk4_0,X1,k3_tmap_1(X2,esk2_0,esk1_0,esk4_0,esk5_0)),k3_tmap_1(X2,esk2_0,esk1_0,X1,esk5_0))
    | ~ m1_pre_topc(esk1_0,X2)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_34]),c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_30]),c_0_39])]),c_0_27])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_38]),c_0_30]),c_0_39])]),c_0_27])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_38]),c_0_30]),c_0_39])]),c_0_27])).

cnf(c_0_50,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_38]),c_0_30]),c_0_39])]),c_0_27])).

cnf(c_0_53,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_38]),c_0_30]),c_0_39])]),c_0_27])).

cnf(c_0_55,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_56,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_58,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(X1,esk2_0,X2,X3,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_47]),c_0_21]),c_0_22])]),c_0_25]),c_0_48]),c_0_49])).

cnf(c_0_59,plain,
    ( r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X4,X2,X5,X6)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(X5) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_50,c_0_14])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_61,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_34]),c_0_21]),c_0_30]),c_0_22]),c_0_39]),c_0_20]),c_0_23]),c_0_24])]),c_0_25]),c_0_27])).

cnf(c_0_62,negated_conjecture,
    ( X1 = k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(esk2_0),X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])]),c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(X1,esk2_0,esk4_0,X2,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_34])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(X1,esk2_0,X2,X3,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0)),u1_struct_0(X3),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_47]),c_0_21]),c_0_22])]),c_0_25]),c_0_48]),c_0_49])).

cnf(c_0_66,negated_conjecture,
    ( r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,X3,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,X3,esk5_0)),X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,X3,esk5_0),X4)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_47]),c_0_21]),c_0_22])]),c_0_25]),c_0_48]),c_0_49])).

cnf(c_0_67,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_70,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_71,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)
    | ~ m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_56])])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_34]),c_0_30]),c_0_39])]),c_0_27])).

cnf(c_0_73,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(X1,esk2_0,esk4_0,X2,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_34])).

cnf(c_0_74,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(X1,esk2_0,X2,X3,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0)))
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_47]),c_0_21]),c_0_22])]),c_0_25]),c_0_48]),c_0_49])).

cnf(c_0_75,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,esk3_0,esk5_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_56])).

cnf(c_0_76,negated_conjecture,
    ( r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk4_0,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),esk6_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(esk6_0,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_34]),c_0_68])]),c_0_36])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_56])])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_34]),c_0_30]),c_0_39])]),c_0_27])).

cnf(c_0_80,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(X1,esk2_0,esk4_0,X2,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_34])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_82,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0)) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_38]),c_0_30]),c_0_39])]),c_0_27])).

cnf(c_0_83,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),esk6_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_55])]),c_0_57])).

cnf(c_0_84,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_56])])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_34]),c_0_30]),c_0_39])]),c_0_27])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_81,c_0_70])).

cnf(c_0_87,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_82]),c_0_56]),c_0_21]),c_0_30]),c_0_22]),c_0_39]),c_0_20]),c_0_23]),c_0_24])]),c_0_25]),c_0_27])).

cnf(c_0_88,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_34]),c_0_30]),c_0_39])]),c_0_27])).

cnf(c_0_89,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_56])])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89]),c_0_90]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:44:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.18/0.38  # and selection function PSelectComplexExceptRRHorn.
% 0.18/0.38  #
% 0.18/0.38  # Preprocessing time       : 0.025 s
% 0.18/0.38  # Presaturation interreduction done
% 0.18/0.38  
% 0.18/0.38  # Proof found!
% 0.18/0.38  # SZS status Theorem
% 0.18/0.38  # SZS output start CNFRefutation
% 0.18/0.38  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.18/0.38  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.18/0.38  fof(t82_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X5,X4),X6))=>r1_tmap_1(X3,X2,k2_tmap_1(X1,X2,X5,X3),X7)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_tmap_1)).
% 0.18/0.38  fof(t79_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X4,X3)&m1_pre_topc(X5,X4))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tmap_1)).
% 0.18/0.38  fof(dt_k3_tmap_1, axiom, ![X1, X2, X3, X4, X5]:(((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&m1_pre_topc(X3,X1))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))&v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 0.18/0.38  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.18/0.38  fof(t81_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(((X6=X7&m1_pre_topc(X4,X3))&r1_tmap_1(X3,X2,X5,X6))=>r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 0.18/0.38  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.18/0.38  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.18/0.38  fof(c_0_9, plain, ![X16, X17, X18, X19, X20]:(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)|(~m1_pre_topc(X18,X16)|(~m1_pre_topc(X19,X16)|(~v1_funct_1(X20)|~v1_funct_2(X20,u1_struct_0(X18),u1_struct_0(X17))|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X17))))|(~m1_pre_topc(X19,X18)|k3_tmap_1(X16,X17,X18,X19,X20)=k2_partfun1(u1_struct_0(X18),u1_struct_0(X17),X20,u1_struct_0(X19)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.18/0.38  fof(c_0_10, plain, ![X33, X34, X35]:(~v2_pre_topc(X33)|~l1_pre_topc(X33)|(~m1_pre_topc(X34,X33)|(~m1_pre_topc(X35,X34)|m1_pre_topc(X35,X33)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.18/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X5,X4),X6))=>r1_tmap_1(X3,X2,k2_tmap_1(X1,X2,X5,X3),X7))))))))))), inference(assume_negation,[status(cth)],[t82_tmap_1])).
% 0.18/0.38  fof(c_0_12, plain, ![X27, X28, X29, X30, X31, X32]:(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|(v2_struct_0(X29)|~m1_pre_topc(X29,X27)|(v2_struct_0(X30)|~m1_pre_topc(X30,X27)|(v2_struct_0(X31)|~m1_pre_topc(X31,X27)|(~m1_pre_topc(X30,X29)|~m1_pre_topc(X31,X30)|(~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X29),u1_struct_0(X28))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X28))))|r2_funct_2(u1_struct_0(X31),u1_struct_0(X28),k3_tmap_1(X27,X28,X30,X31,k3_tmap_1(X27,X28,X29,X30,X32)),k3_tmap_1(X27,X28,X29,X31,X32))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_tmap_1])])])])).
% 0.18/0.38  cnf(c_0_13, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.38  cnf(c_0_14, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(m1_pre_topc(esk3_0,esk4_0)&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(m1_subset_1(esk7_0,u1_struct_0(esk3_0))&((esk6_0=esk7_0&r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk6_0))&~r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk7_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.18/0.38  cnf(c_0_16, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|v2_struct_0(X5)|r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X5,X1)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X5,X4)|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.38  fof(c_0_17, plain, ![X21, X22, X23, X24, X25]:(((v1_funct_1(k3_tmap_1(X21,X22,X23,X24,X25))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|~m1_pre_topc(X23,X21)|~m1_pre_topc(X24,X21)|~v1_funct_1(X25)|~v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X22))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22))))))&(v1_funct_2(k3_tmap_1(X21,X22,X23,X24,X25),u1_struct_0(X24),u1_struct_0(X22))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|~m1_pre_topc(X23,X21)|~m1_pre_topc(X24,X21)|~v1_funct_1(X25)|~v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X22))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22)))))))&(m1_subset_1(k3_tmap_1(X21,X22,X23,X24,X25),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X22))))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|~m1_pre_topc(X23,X21)|~m1_pre_topc(X24,X21)|~v1_funct_1(X25)|~v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X22))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).
% 0.18/0.38  fof(c_0_18, plain, ![X26]:(~l1_pre_topc(X26)|m1_pre_topc(X26,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.18/0.38  cnf(c_0_19, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)), inference(csr,[status(thm)],[c_0_13, c_0_14])).
% 0.18/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_26, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|v2_struct_0(X5)|r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6))|~m1_pre_topc(X5,X4)|~m1_pre_topc(X5,X1)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X6)), inference(csr,[status(thm)],[c_0_16, c_0_14])).
% 0.18/0.38  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_28, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.38  cnf(c_0_29, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.38  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_31, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.38  cnf(c_0_32, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.38  cnf(c_0_33, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.18/0.38  cnf(c_0_34, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_35, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r2_funct_2(u1_struct_0(X3),u1_struct_0(esk2_0),k3_tmap_1(X1,esk2_0,X2,X3,k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0)),k3_tmap_1(X1,esk2_0,esk1_0,X3,esk5_0))|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_27]), c_0_25])).
% 0.18/0.38  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_37, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.18/0.38  cnf(c_0_38, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.38  cnf(c_0_39, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_40, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0))|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.18/0.38  cnf(c_0_41, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0),u1_struct_0(X2),u1_struct_0(esk2_0))|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.18/0.38  fof(c_0_42, plain, ![X36, X37, X38, X39, X40, X41, X42]:(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|(v2_struct_0(X38)|~m1_pre_topc(X38,X36)|(v2_struct_0(X39)|~m1_pre_topc(X39,X36)|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X37))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X37))))|(~m1_subset_1(X41,u1_struct_0(X38))|(~m1_subset_1(X42,u1_struct_0(X39))|(X41!=X42|~m1_pre_topc(X39,X38)|~r1_tmap_1(X38,X37,X40,X41)|r1_tmap_1(X39,X37,k3_tmap_1(X36,X37,X38,X39,X40),X42))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t81_tmap_1])])])])).
% 0.18/0.38  fof(c_0_43, plain, ![X12, X13, X14, X15]:(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)|(~v1_funct_1(X14)|~v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))|(~m1_pre_topc(X15,X12)|k2_tmap_1(X12,X13,X14,X15)=k2_partfun1(u1_struct_0(X12),u1_struct_0(X13),X14,u1_struct_0(X15)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.18/0.38  cnf(c_0_44, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,esk4_0,esk5_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))|v2_struct_0(X1)|~m1_pre_topc(esk1_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.38  fof(c_0_45, plain, ![X8, X9, X10, X11]:((~r2_funct_2(X8,X9,X10,X11)|X10=X11|(~v1_funct_1(X10)|~v1_funct_2(X10,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|~v1_funct_1(X11)|~v1_funct_2(X11,X8,X9)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))&(X10!=X11|r2_funct_2(X8,X9,X10,X11)|(~v1_funct_1(X10)|~v1_funct_2(X10,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|~v1_funct_1(X11)|~v1_funct_2(X11,X8,X9)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.18/0.38  cnf(c_0_46, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(X2,esk2_0,esk4_0,X1,k3_tmap_1(X2,esk2_0,esk1_0,esk4_0,esk5_0)),k3_tmap_1(X2,esk2_0,esk1_0,X1,esk5_0))|~m1_pre_topc(esk1_0,X2)|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_34]), c_0_36])).
% 0.18/0.38  cnf(c_0_47, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_30]), c_0_39])]), c_0_27])).
% 0.18/0.38  cnf(c_0_48, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_38]), c_0_30]), c_0_39])]), c_0_27])).
% 0.18/0.38  cnf(c_0_49, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_38]), c_0_30]), c_0_39])]), c_0_27])).
% 0.18/0.38  cnf(c_0_50, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,u1_struct_0(X4))|X6!=X7|~m1_pre_topc(X4,X3)|~r1_tmap_1(X3,X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.38  cnf(c_0_51, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.38  cnf(c_0_52, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_38]), c_0_30]), c_0_39])]), c_0_27])).
% 0.18/0.38  cnf(c_0_53, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.38  cnf(c_0_54, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0))|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_38]), c_0_30]), c_0_39])]), c_0_27])).
% 0.18/0.38  cnf(c_0_55, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_56, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_57, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_58, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(X1,esk2_0,X2,X3,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(esk2_0))))|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_47]), c_0_21]), c_0_22])]), c_0_25]), c_0_48]), c_0_49])).
% 0.18/0.38  cnf(c_0_59, plain, (r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X4,X2,X5,X6)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X4,X3)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~v2_pre_topc(X3)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X4))|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~v1_funct_1(X5)), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_50, c_0_14])])).
% 0.18/0.38  cnf(c_0_60, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.38  cnf(c_0_61, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_34]), c_0_21]), c_0_30]), c_0_22]), c_0_39]), c_0_20]), c_0_23]), c_0_24])]), c_0_25]), c_0_27])).
% 0.18/0.39  cnf(c_0_62, negated_conjecture, (X1=k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0)|~m1_pre_topc(X2,esk1_0)|~r2_funct_2(u1_struct_0(X2),u1_struct_0(esk2_0),X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_47]), c_0_48]), c_0_49])).
% 0.18/0.39  cnf(c_0_63, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])]), c_0_57])).
% 0.18/0.39  cnf(c_0_64, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(X1,esk2_0,esk4_0,X2,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_58, c_0_34])).
% 0.18/0.39  cnf(c_0_65, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(X1,esk2_0,X2,X3,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0)),u1_struct_0(X3),u1_struct_0(esk2_0))|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_47]), c_0_21]), c_0_22])]), c_0_25]), c_0_48]), c_0_49])).
% 0.18/0.39  cnf(c_0_66, negated_conjecture, (r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,X3,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,X3,esk5_0)),X4)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X3,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,X3,esk5_0),X4)|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_47]), c_0_21]), c_0_22])]), c_0_25]), c_0_48]), c_0_49])).
% 0.18/0.39  cnf(c_0_67, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0),esk6_0)), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.18/0.39  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.39  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.39  cnf(c_0_70, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.39  cnf(c_0_71, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0))=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)|~m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))|~v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_56])])).
% 0.18/0.39  cnf(c_0_72, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_34]), c_0_30]), c_0_39])]), c_0_27])).
% 0.18/0.39  cnf(c_0_73, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(X1,esk2_0,esk4_0,X2,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),u1_struct_0(X2),u1_struct_0(esk2_0))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_65, c_0_34])).
% 0.18/0.39  cnf(c_0_74, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(X1,esk2_0,X2,X3,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0)))|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_47]), c_0_21]), c_0_22])]), c_0_25]), c_0_48]), c_0_49])).
% 0.18/0.39  cnf(c_0_75, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,esk3_0,esk5_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))|v2_struct_0(X1)|~m1_pre_topc(esk1_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_56])).
% 0.18/0.39  cnf(c_0_76, negated_conjecture, (r1_tmap_1(X1,esk2_0,k3_tmap_1(X2,esk2_0,esk4_0,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),esk6_0)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(esk4_0,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(esk6_0,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_34]), c_0_68])]), c_0_36])).
% 0.18/0.39  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.18/0.39  cnf(c_0_78, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0))=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)|~v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_56])])).
% 0.18/0.39  cnf(c_0_79, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_34]), c_0_30]), c_0_39])]), c_0_27])).
% 0.18/0.39  cnf(c_0_80, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(X1,esk2_0,esk4_0,X2,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_74, c_0_34])).
% 0.18/0.39  cnf(c_0_81, negated_conjecture, (~r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.39  cnf(c_0_82, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_38]), c_0_30]), c_0_39])]), c_0_27])).
% 0.18/0.39  cnf(c_0_83, negated_conjecture, (r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),esk6_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_55])]), c_0_57])).
% 0.18/0.39  cnf(c_0_84, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0))=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)|~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_56])])).
% 0.18/0.39  cnf(c_0_85, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_34]), c_0_30]), c_0_39])]), c_0_27])).
% 0.18/0.39  cnf(c_0_86, negated_conjecture, (~r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(rw,[status(thm)],[c_0_81, c_0_70])).
% 0.18/0.39  cnf(c_0_87, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_82]), c_0_56]), c_0_21]), c_0_30]), c_0_22]), c_0_39]), c_0_20]), c_0_23]), c_0_24])]), c_0_25]), c_0_27])).
% 0.18/0.39  cnf(c_0_88, negated_conjecture, (r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_34]), c_0_30]), c_0_39])]), c_0_27])).
% 0.18/0.39  cnf(c_0_89, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0))=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_56])])).
% 0.18/0.39  cnf(c_0_90, negated_conjecture, (~r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),esk6_0)), inference(rw,[status(thm)],[c_0_86, c_0_87])).
% 0.18/0.39  cnf(c_0_91, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89]), c_0_90]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 92
% 0.18/0.39  # Proof object clause steps            : 73
% 0.18/0.39  # Proof object formula steps           : 19
% 0.18/0.39  # Proof object conjectures             : 63
% 0.18/0.39  # Proof object clause conjectures      : 60
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 29
% 0.18/0.39  # Proof object initial formulas used   : 9
% 0.18/0.39  # Proof object generating inferences   : 36
% 0.18/0.39  # Proof object simplifying inferences  : 148
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 9
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 30
% 0.18/0.39  # Removed in clause preprocessing      : 0
% 0.18/0.39  # Initial clauses in saturation        : 30
% 0.18/0.39  # Processed clauses                    : 203
% 0.18/0.39  # ...of these trivial                  : 4
% 0.18/0.39  # ...subsumed                          : 22
% 0.18/0.39  # ...remaining for further processing  : 177
% 0.18/0.39  # Other redundant clauses eliminated   : 2
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 3
% 0.18/0.39  # Backward-rewritten                   : 20
% 0.18/0.39  # Generated clauses                    : 239
% 0.18/0.39  # ...of the previous two non-trivial   : 213
% 0.18/0.39  # Contextual simplify-reflections      : 38
% 0.18/0.39  # Paramodulations                      : 237
% 0.18/0.39  # Factorizations                       : 0
% 0.18/0.39  # Equation resolutions                 : 2
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 122
% 0.18/0.39  #    Positive orientable unit clauses  : 24
% 0.18/0.39  #    Positive unorientable unit clauses: 0
% 0.18/0.39  #    Negative unit clauses             : 5
% 0.18/0.39  #    Non-unit-clauses                  : 93
% 0.18/0.39  # Current number of unprocessed clauses: 68
% 0.18/0.39  # ...number of literals in the above   : 663
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 53
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 8150
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 624
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 62
% 0.18/0.39  # Unit Clause-clause subsumption calls : 73
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 42
% 0.18/0.39  # BW rewrite match successes           : 8
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 19400
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.049 s
% 0.18/0.39  # System time              : 0.006 s
% 0.18/0.39  # Total time               : 0.055 s
% 0.18/0.39  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
