%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:31 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   92 (3188 expanded)
%              Number of clauses        :   73 (1000 expanded)
%              Number of leaves         :    9 ( 786 expanded)
%              Depth                    :   12
%              Number of atoms          :  636 (48302 expanded)
%              Number of equality atoms :   45 (5883 expanded)
%              Maximal formula depth    :   32 (   7 average)
%              Maximal clause size      :   61 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t74_tmap_1,axiom,(
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
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                 => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t125_tmap_1,conjecture,(
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
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ( X1 = k1_tsep_1(X1,X4,X5)
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X1))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X4))
                               => ! [X8] :
                                    ( m1_subset_1(X8,u1_struct_0(X5))
                                   => ( ( X6 = X7
                                        & X6 = X8 )
                                     => ( r1_tmap_1(X1,X2,X3,X6)
                                      <=> ( r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)
                                          & r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t124_tmap_1,axiom,(
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
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X4,X5)))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X4))
                             => ! [X8] :
                                  ( m1_subset_1(X8,u1_struct_0(X5))
                                 => ( ( X6 = X7
                                      & X6 = X8 )
                                   => ( r1_tmap_1(k1_tsep_1(X1,X4,X5),X2,k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),X6)
                                    <=> ( r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)
                                        & r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_tmap_1)).

fof(c_0_9,plain,(
    ! [X36,X37,X38,X39] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | v2_struct_0(X37)
      | ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | v2_struct_0(X38)
      | ~ m1_pre_topc(X38,X36)
      | ~ v1_funct_1(X39)
      | ~ v1_funct_2(X39,u1_struct_0(X38),u1_struct_0(X37))
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X37))))
      | r2_funct_2(u1_struct_0(X38),u1_struct_0(X37),X39,k3_tmap_1(X36,X37,X38,X38,X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_tmap_1])])])])).

fof(c_0_10,plain,(
    ! [X35] :
      ( ~ l1_pre_topc(X35)
      | m1_pre_topc(X35,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

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
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( ~ v2_struct_0(X5)
                          & m1_pre_topc(X5,X1) )
                       => ( X1 = k1_tsep_1(X1,X4,X5)
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X1))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ! [X8] :
                                      ( m1_subset_1(X8,u1_struct_0(X5))
                                     => ( ( X6 = X7
                                          & X6 = X8 )
                                       => ( r1_tmap_1(X1,X2,X3,X6)
                                        <=> ( r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)
                                            & r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t125_tmap_1])).

fof(c_0_12,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( v2_struct_0(X18)
      | ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_pre_topc(X20,X18)
      | ~ m1_pre_topc(X21,X18)
      | ~ v1_funct_1(X22)
      | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X19))
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X19))))
      | ~ m1_pre_topc(X21,X20)
      | k3_tmap_1(X18,X19,X20,X21,X22) = k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),X22,u1_struct_0(X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_13,plain,(
    ! [X14,X15,X16,X17] :
      ( v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ v1_funct_1(X16)
      | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))
      | ~ m1_pre_topc(X17,X14)
      | k2_tmap_1(X14,X15,X16,X17) = k2_partfun1(u1_struct_0(X14),u1_struct_0(X15),X16,u1_struct_0(X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    & esk6_0 = esk7_0
    & esk6_0 = esk8_0
    & ( ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)
      | ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
      | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0) )
    & ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
      | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) )
    & ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)
      | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

cnf(c_0_17,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X23,X24,X25,X26] :
      ( ( v1_funct_1(k2_tmap_1(X23,X24,X25,X26))
        | ~ l1_struct_0(X23)
        | ~ l1_struct_0(X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))
        | ~ l1_struct_0(X26) )
      & ( v1_funct_2(k2_tmap_1(X23,X24,X25,X26),u1_struct_0(X26),u1_struct_0(X24))
        | ~ l1_struct_0(X23)
        | ~ l1_struct_0(X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))
        | ~ l1_struct_0(X26) )
      & ( m1_subset_1(k2_tmap_1(X23,X24,X25,X26),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X24))))
        | ~ l1_struct_0(X23)
        | ~ l1_struct_0(X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))
        | ~ l1_struct_0(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

fof(c_0_20,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ r2_funct_2(X9,X10,X11,X12)
        | X11 = X12
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X9,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( X11 != X12
        | r2_funct_2(X9,X10,X11,X12)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X9,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X2,X1,X2,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( k3_tmap_1(X1,X2,X3,X3,X4) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X4,u1_struct_0(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_32,plain,
    ( k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X1)) = k2_tmap_1(X1,X2,X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_33,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_34,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | l1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_35,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_36,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_37,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33,X34] :
      ( ( r1_tmap_1(X30,X28,k2_tmap_1(X27,X28,X29,X30),X33)
        | ~ r1_tmap_1(k1_tsep_1(X27,X30,X31),X28,k2_tmap_1(X27,X28,X29,k1_tsep_1(X27,X30,X31)),X32)
        | X32 != X33
        | X32 != X34
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(k1_tsep_1(X27,X30,X31)))
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X27)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X27)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( r1_tmap_1(X31,X28,k2_tmap_1(X27,X28,X29,X31),X34)
        | ~ r1_tmap_1(k1_tsep_1(X27,X30,X31),X28,k2_tmap_1(X27,X28,X29,k1_tsep_1(X27,X30,X31)),X32)
        | X32 != X33
        | X32 != X34
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(k1_tsep_1(X27,X30,X31)))
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X27)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X27)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ r1_tmap_1(X30,X28,k2_tmap_1(X27,X28,X29,X30),X33)
        | ~ r1_tmap_1(X31,X28,k2_tmap_1(X27,X28,X29,X31),X34)
        | r1_tmap_1(k1_tsep_1(X27,X30,X31),X28,k2_tmap_1(X27,X28,X29,k1_tsep_1(X27,X30,X31)),X32)
        | X32 != X33
        | X32 != X34
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ m1_subset_1(X33,u1_struct_0(X30))
        | ~ m1_subset_1(X32,u1_struct_0(k1_tsep_1(X27,X30,X31)))
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X27)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X27)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t124_tmap_1])])])])])).

cnf(c_0_38,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_30])).

cnf(c_0_40,plain,
    ( k3_tmap_1(X1,X2,X1,X1,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X1))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk1_0)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_30]),c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_27]),c_0_28])])).

cnf(c_0_43,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_22]),c_0_27]),c_0_28])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_22]),c_0_27]),c_0_28])])).

cnf(c_0_46,plain,
    ( r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X8)
    | v2_struct_0(X6)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | ~ r1_tmap_1(X6,X2,k2_tmap_1(X3,X2,X4,X6),X7)
    | X8 != X5
    | X8 != X7
    | ~ m1_subset_1(X7,u1_struct_0(X6))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X8,u1_struct_0(k1_tsep_1(X3,X1,X6)))
    | ~ m1_pre_topc(X6,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_48,negated_conjecture,
    ( esk6_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_50,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk3_0) = esk3_0
    | ~ m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_27]),c_0_22]),c_0_28])])).

cnf(c_0_51,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk3_0) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_22]),c_0_41]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_30])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_25])])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_43]),c_0_25])])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_43]),c_0_25])])).

cnf(c_0_55,plain,
    ( r1_tmap_1(k1_tsep_1(X1,X2,X3),X4,k2_tmap_1(X1,X4,X5,k1_tsep_1(X1,X2,X3)),X6)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,X4,k2_tmap_1(X1,X4,X5,X3),X6)
    | ~ r1_tmap_1(X2,X4,k2_tmap_1(X1,X4,X5,X2),X6)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X6,u1_struct_0(X2))
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
    | ~ v1_funct_1(X5) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_60,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_61,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_63,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0) = esk3_0
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_51]),c_0_51]),c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_43]),c_0_26])])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_43]),c_0_26])])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_43]),c_0_26])])).

cnf(c_0_67,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X6)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(k1_tsep_1(X3,X6,X1),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X6,X1)),X7)
    | X7 != X8
    | X7 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X8,u1_struct_0(X6))
    | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X6,X1)))
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X6,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_68,negated_conjecture,
    ( r1_tmap_1(k1_tsep_1(esk1_0,X1,esk5_0),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk5_0)),esk6_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),esk6_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(esk1_0,X1,esk5_0)))
    | ~ m1_subset_1(esk6_0,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_24]),c_0_23]),c_0_26]),c_0_25]),c_0_27]),c_0_58]),c_0_22]),c_0_28])]),c_0_29]),c_0_30]),c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_71,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_61])).

cnf(c_0_74,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_75,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0) = esk3_0
    | ~ l1_struct_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_66])).

cnf(c_0_76,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X6)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(k1_tsep_1(X3,X6,X1),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X6,X1)),X5)
    | ~ m1_pre_topc(X6,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X3,X6,X1)))
    | ~ m1_subset_1(X5,u1_struct_0(X6))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_67])])).

cnf(c_0_77,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X6)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X7)
    | X7 != X5
    | X7 != X8
    | ~ m1_subset_1(X8,u1_struct_0(X6))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X1,X6)))
    | ~ m1_pre_topc(X6,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)
    | ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_79,negated_conjecture,
    ( r1_tmap_1(esk1_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0),esk6_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_70]),c_0_71]),c_0_70]),c_0_72]),c_0_73])]),c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_43]),c_0_26])])).

cnf(c_0_81,negated_conjecture,
    ( r1_tmap_1(esk5_0,X1,k2_tmap_1(esk1_0,X1,X2,esk5_0),X3)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk1_0,X1,k2_tmap_1(esk1_0,X1,X2,esk1_0),X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk5_0))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_70]),c_0_71]),c_0_57]),c_0_24]),c_0_26])]),c_0_59]),c_0_30]),c_0_74])).

cnf(c_0_82,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X6)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X5)
    | ~ m1_pre_topc(X6,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X3,X1,X6)))
    | ~ m1_subset_1(X5,u1_struct_0(X6))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_77])])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)
    | ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_61]),c_0_48])).

cnf(c_0_84,negated_conjecture,
    ( r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_85,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),X1)
    | ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_80]),c_0_23]),c_0_25]),c_0_27]),c_0_22]),c_0_28])]),c_0_29])).

cnf(c_0_86,negated_conjecture,
    ( r1_tmap_1(esk4_0,X1,k2_tmap_1(esk1_0,X1,X2,esk4_0),X3)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk1_0,X1,k2_tmap_1(esk1_0,X1,X2,esk1_0),X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_70]),c_0_57]),c_0_71]),c_0_24]),c_0_26])]),c_0_74]),c_0_30]),c_0_59])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])])).

cnf(c_0_88,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_84]),c_0_72]),c_0_73]),c_0_58])])).

cnf(c_0_89,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)
    | ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_80]),c_0_23]),c_0_25]),c_0_27]),c_0_22]),c_0_28])]),c_0_29])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_84]),c_0_72]),c_0_58]),c_0_73])]),c_0_90]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:47:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.42  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.18/0.42  # and selection function SelectCQIPrecWNTNp.
% 0.18/0.42  #
% 0.18/0.42  # Preprocessing time       : 0.030 s
% 0.18/0.42  # Presaturation interreduction done
% 0.18/0.42  
% 0.18/0.42  # Proof found!
% 0.18/0.42  # SZS status Theorem
% 0.18/0.42  # SZS output start CNFRefutation
% 0.18/0.42  fof(t74_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 0.18/0.42  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.18/0.42  fof(t125_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>(X1=k1_tsep_1(X1,X4,X5)=>![X6]:(m1_subset_1(X6,u1_struct_0(X1))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(X1,X2,X3,X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_tmap_1)).
% 0.18/0.42  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.18/0.42  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.18/0.42  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 0.18/0.42  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.18/0.42  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.18/0.42  fof(t124_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>![X6]:(m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X4,X5)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(k1_tsep_1(X1,X4,X5),X2,k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_tmap_1)).
% 0.18/0.42  fof(c_0_9, plain, ![X36, X37, X38, X39]:(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|(v2_struct_0(X38)|~m1_pre_topc(X38,X36)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X38),u1_struct_0(X37))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X37))))|r2_funct_2(u1_struct_0(X38),u1_struct_0(X37),X39,k3_tmap_1(X36,X37,X38,X38,X39)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_tmap_1])])])])).
% 0.18/0.42  fof(c_0_10, plain, ![X35]:(~l1_pre_topc(X35)|m1_pre_topc(X35,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.18/0.42  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>(X1=k1_tsep_1(X1,X4,X5)=>![X6]:(m1_subset_1(X6,u1_struct_0(X1))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(X1,X2,X3,X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8)))))))))))))), inference(assume_negation,[status(cth)],[t125_tmap_1])).
% 0.18/0.42  fof(c_0_12, plain, ![X18, X19, X20, X21, X22]:(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|(~m1_pre_topc(X20,X18)|(~m1_pre_topc(X21,X18)|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X19))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X19))))|(~m1_pre_topc(X21,X20)|k3_tmap_1(X18,X19,X20,X21,X22)=k2_partfun1(u1_struct_0(X20),u1_struct_0(X19),X22,u1_struct_0(X21)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.18/0.42  fof(c_0_13, plain, ![X14, X15, X16, X17]:(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X15))))|(~m1_pre_topc(X17,X14)|k2_tmap_1(X14,X15,X16,X17)=k2_partfun1(u1_struct_0(X14),u1_struct_0(X15),X16,u1_struct_0(X17)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.18/0.42  cnf(c_0_14, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.42  cnf(c_0_15, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.42  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&(esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)&(m1_subset_1(esk6_0,u1_struct_0(esk1_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&((esk6_0=esk7_0&esk6_0=esk8_0)&((~r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)|(~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)))&((r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0))&(r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)))))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).
% 0.18/0.42  cnf(c_0_17, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.42  cnf(c_0_18, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.42  fof(c_0_19, plain, ![X23, X24, X25, X26]:(((v1_funct_1(k2_tmap_1(X23,X24,X25,X26))|(~l1_struct_0(X23)|~l1_struct_0(X24)|~v1_funct_1(X25)|~v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))|~l1_struct_0(X26)))&(v1_funct_2(k2_tmap_1(X23,X24,X25,X26),u1_struct_0(X26),u1_struct_0(X24))|(~l1_struct_0(X23)|~l1_struct_0(X24)|~v1_funct_1(X25)|~v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))|~l1_struct_0(X26))))&(m1_subset_1(k2_tmap_1(X23,X24,X25,X26),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X24))))|(~l1_struct_0(X23)|~l1_struct_0(X24)|~v1_funct_1(X25)|~v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))|~l1_struct_0(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 0.18/0.42  fof(c_0_20, plain, ![X9, X10, X11, X12]:((~r2_funct_2(X9,X10,X11,X12)|X11=X12|(~v1_funct_1(X11)|~v1_funct_2(X11,X9,X10)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|~v1_funct_1(X12)|~v1_funct_2(X12,X9,X10)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))&(X11!=X12|r2_funct_2(X9,X10,X11,X12)|(~v1_funct_1(X11)|~v1_funct_2(X11,X9,X10)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|~v1_funct_1(X12)|~v1_funct_2(X12,X9,X10)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.18/0.42  cnf(c_0_21, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X2,X1,X2,X2,X3))|~v2_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X3)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.18/0.42  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_24, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_31, plain, (k3_tmap_1(X1,X2,X3,X3,X4)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X4,u1_struct_0(X3))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~l1_pre_topc(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)), inference(spm,[status(thm)],[c_0_17, c_0_15])).
% 0.18/0.42  cnf(c_0_32, plain, (k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X1))=k2_tmap_1(X1,X2,X3,X1)|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)), inference(spm,[status(thm)],[c_0_18, c_0_15])).
% 0.18/0.42  cnf(c_0_33, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.42  fof(c_0_34, plain, ![X13]:(~l1_pre_topc(X13)|l1_struct_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.18/0.42  cnf(c_0_35, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.42  cnf(c_0_36, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.42  fof(c_0_37, plain, ![X27, X28, X29, X30, X31, X32, X33, X34]:(((r1_tmap_1(X30,X28,k2_tmap_1(X27,X28,X29,X30),X33)|~r1_tmap_1(k1_tsep_1(X27,X30,X31),X28,k2_tmap_1(X27,X28,X29,k1_tsep_1(X27,X30,X31)),X32)|(X32!=X33|X32!=X34)|~m1_subset_1(X34,u1_struct_0(X31))|~m1_subset_1(X33,u1_struct_0(X30))|~m1_subset_1(X32,u1_struct_0(k1_tsep_1(X27,X30,X31)))|(v2_struct_0(X31)|~m1_pre_topc(X31,X27))|(v2_struct_0(X30)|~m1_pre_topc(X30,X27))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(r1_tmap_1(X31,X28,k2_tmap_1(X27,X28,X29,X31),X34)|~r1_tmap_1(k1_tsep_1(X27,X30,X31),X28,k2_tmap_1(X27,X28,X29,k1_tsep_1(X27,X30,X31)),X32)|(X32!=X33|X32!=X34)|~m1_subset_1(X34,u1_struct_0(X31))|~m1_subset_1(X33,u1_struct_0(X30))|~m1_subset_1(X32,u1_struct_0(k1_tsep_1(X27,X30,X31)))|(v2_struct_0(X31)|~m1_pre_topc(X31,X27))|(v2_struct_0(X30)|~m1_pre_topc(X30,X27))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27))))&(~r1_tmap_1(X30,X28,k2_tmap_1(X27,X28,X29,X30),X33)|~r1_tmap_1(X31,X28,k2_tmap_1(X27,X28,X29,X31),X34)|r1_tmap_1(k1_tsep_1(X27,X30,X31),X28,k2_tmap_1(X27,X28,X29,k1_tsep_1(X27,X30,X31)),X32)|(X32!=X33|X32!=X34)|~m1_subset_1(X34,u1_struct_0(X31))|~m1_subset_1(X33,u1_struct_0(X30))|~m1_subset_1(X32,u1_struct_0(k1_tsep_1(X27,X30,X31)))|(v2_struct_0(X31)|~m1_pre_topc(X31,X27))|(v2_struct_0(X30)|~m1_pre_topc(X30,X27))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t124_tmap_1])])])])])).
% 0.18/0.42  cnf(c_0_38, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.42  cnf(c_0_39, negated_conjecture, (r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_30])).
% 0.18/0.42  cnf(c_0_40, plain, (k3_tmap_1(X1,X2,X1,X1,X3)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X1))|v2_struct_0(X2)|v2_struct_0(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)), inference(spm,[status(thm)],[c_0_31, c_0_15])).
% 0.18/0.42  cnf(c_0_41, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk1_0))=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_30]), c_0_29])).
% 0.18/0.42  cnf(c_0_42, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_22]), c_0_27]), c_0_28])])).
% 0.18/0.42  cnf(c_0_43, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.42  cnf(c_0_44, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_22]), c_0_27]), c_0_28])])).
% 0.18/0.42  cnf(c_0_45, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_22]), c_0_27]), c_0_28])])).
% 0.18/0.42  cnf(c_0_46, plain, (r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X8)|v2_struct_0(X6)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|~r1_tmap_1(X6,X2,k2_tmap_1(X3,X2,X4,X6),X7)|X8!=X5|X8!=X7|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X8,u1_struct_0(k1_tsep_1(X3,X1,X6)))|~m1_pre_topc(X6,X3)|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.42  cnf(c_0_47, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_48, negated_conjecture, (esk6_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_50, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk3_0)=esk3_0|~m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|~v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_27]), c_0_22]), c_0_28])])).
% 0.18/0.42  cnf(c_0_51, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk3_0)=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_22]), c_0_41]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_30])).
% 0.18/0.42  cnf(c_0_52, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_25])])).
% 0.18/0.42  cnf(c_0_53, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_43]), c_0_25])])).
% 0.18/0.42  cnf(c_0_54, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_43]), c_0_25])])).
% 0.18/0.42  cnf(c_0_55, plain, (r1_tmap_1(k1_tsep_1(X1,X2,X3),X4,k2_tmap_1(X1,X4,X5,k1_tsep_1(X1,X2,X3)),X6)|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|~r1_tmap_1(X3,X4,k2_tmap_1(X1,X4,X5,X3),X6)|~r1_tmap_1(X2,X4,k2_tmap_1(X1,X4,X5,X2),X6)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~v2_pre_topc(X4)|~l1_pre_topc(X1)|~l1_pre_topc(X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))|~m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X2,X3)))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X6,u1_struct_0(X2))|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))|~v1_funct_1(X5)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).
% 0.18/0.42  cnf(c_0_56, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.18/0.42  cnf(c_0_57, negated_conjecture, (m1_pre_topc(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_49, c_0_48])).
% 0.18/0.42  cnf(c_0_59, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_60, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_61, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_63, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0)=esk3_0|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_51]), c_0_51]), c_0_51])).
% 0.18/0.42  cnf(c_0_64, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_43]), c_0_26])])).
% 0.18/0.42  cnf(c_0_65, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_43]), c_0_26])])).
% 0.18/0.42  cnf(c_0_66, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_43]), c_0_26])])).
% 0.18/0.42  cnf(c_0_67, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X6)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(k1_tsep_1(X3,X6,X1),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X6,X1)),X7)|X7!=X8|X7!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X6,X1)))|~m1_pre_topc(X1,X3)|~m1_pre_topc(X6,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.42  cnf(c_0_68, negated_conjecture, (r1_tmap_1(k1_tsep_1(esk1_0,X1,esk5_0),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk5_0)),esk6_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)|v2_struct_0(X1)|~r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),esk6_0)|~m1_pre_topc(X1,esk1_0)|~m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(esk1_0,X1,esk5_0)))|~m1_subset_1(esk6_0,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_24]), c_0_23]), c_0_26]), c_0_25]), c_0_27]), c_0_58]), c_0_22]), c_0_28])]), c_0_29]), c_0_30]), c_0_59])).
% 0.18/0.42  cnf(c_0_69, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.18/0.42  cnf(c_0_70, negated_conjecture, (esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_71, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_62, c_0_61])).
% 0.18/0.42  cnf(c_0_74, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_75, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0)=esk3_0|~l1_struct_0(esk1_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_66])).
% 0.18/0.42  cnf(c_0_76, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X6)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tmap_1(k1_tsep_1(X3,X6,X1),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X6,X1)),X5)|~m1_pre_topc(X6,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X3,X6,X1)))|~m1_subset_1(X5,u1_struct_0(X6))|~m1_subset_1(X5,u1_struct_0(X1))|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_67])])).
% 0.18/0.42  cnf(c_0_77, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X6)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X7)|X7!=X5|X7!=X8|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X1,X6)))|~m1_pre_topc(X6,X3)|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.42  cnf(c_0_78, negated_conjecture, (~r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)|~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.42  cnf(c_0_79, negated_conjecture, (r1_tmap_1(esk1_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0),esk6_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_70]), c_0_71]), c_0_70]), c_0_72]), c_0_73])]), c_0_74])).
% 0.18/0.42  cnf(c_0_80, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_43]), c_0_26])])).
% 0.18/0.42  cnf(c_0_81, negated_conjecture, (r1_tmap_1(esk5_0,X1,k2_tmap_1(esk1_0,X1,X2,esk5_0),X3)|v2_struct_0(X1)|~r1_tmap_1(esk1_0,X1,k2_tmap_1(esk1_0,X1,X2,esk1_0),X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~m1_subset_1(X3,u1_struct_0(esk1_0))|~m1_subset_1(X3,u1_struct_0(esk4_0))|~m1_subset_1(X3,u1_struct_0(esk5_0))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_70]), c_0_71]), c_0_57]), c_0_24]), c_0_26])]), c_0_59]), c_0_30]), c_0_74])).
% 0.18/0.42  cnf(c_0_82, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X6)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X5)|~m1_pre_topc(X6,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X3,X1,X6)))|~m1_subset_1(X5,u1_struct_0(X6))|~m1_subset_1(X5,u1_struct_0(X1))|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_77])])).
% 0.18/0.42  cnf(c_0_83, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)|~r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_61]), c_0_48])).
% 0.18/0.42  cnf(c_0_84, negated_conjecture, (r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])])).
% 0.18/0.42  cnf(c_0_85, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),X1)|~r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_80]), c_0_23]), c_0_25]), c_0_27]), c_0_22]), c_0_28])]), c_0_29])).
% 0.18/0.42  cnf(c_0_86, negated_conjecture, (r1_tmap_1(esk4_0,X1,k2_tmap_1(esk1_0,X1,X2,esk4_0),X3)|v2_struct_0(X1)|~r1_tmap_1(esk1_0,X1,k2_tmap_1(esk1_0,X1,X2,esk1_0),X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~m1_subset_1(X3,u1_struct_0(esk1_0))|~m1_subset_1(X3,u1_struct_0(esk5_0))|~m1_subset_1(X3,u1_struct_0(esk4_0))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_70]), c_0_57]), c_0_71]), c_0_24]), c_0_26])]), c_0_74]), c_0_30]), c_0_59])).
% 0.18/0.42  cnf(c_0_87, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84])])).
% 0.18/0.42  cnf(c_0_88, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_84]), c_0_72]), c_0_73]), c_0_58])])).
% 0.18/0.42  cnf(c_0_89, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)|~r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_80]), c_0_23]), c_0_25]), c_0_27]), c_0_22]), c_0_28])]), c_0_29])).
% 0.18/0.42  cnf(c_0_90, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88])])).
% 0.18/0.42  cnf(c_0_91, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_84]), c_0_72]), c_0_58]), c_0_73])]), c_0_90]), ['proof']).
% 0.18/0.42  # SZS output end CNFRefutation
% 0.18/0.42  # Proof object total steps             : 92
% 0.18/0.42  # Proof object clause steps            : 73
% 0.18/0.42  # Proof object formula steps           : 19
% 0.18/0.42  # Proof object conjectures             : 57
% 0.18/0.42  # Proof object clause conjectures      : 54
% 0.18/0.42  # Proof object formula conjectures     : 3
% 0.18/0.42  # Proof object initial clauses used    : 34
% 0.18/0.42  # Proof object initial formulas used   : 9
% 0.18/0.42  # Proof object generating inferences   : 27
% 0.18/0.42  # Proof object simplifying inferences  : 139
% 0.18/0.42  # Training examples: 0 positive, 0 negative
% 0.18/0.42  # Parsed axioms                        : 9
% 0.18/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.42  # Initial clauses                      : 35
% 0.18/0.42  # Removed in clause preprocessing      : 0
% 0.18/0.42  # Initial clauses in saturation        : 35
% 0.18/0.42  # Processed clauses                    : 398
% 0.18/0.42  # ...of these trivial                  : 2
% 0.18/0.42  # ...subsumed                          : 91
% 0.18/0.42  # ...remaining for further processing  : 305
% 0.18/0.42  # Other redundant clauses eliminated   : 7
% 0.18/0.42  # Clauses deleted for lack of memory   : 0
% 0.18/0.42  # Backward-subsumed                    : 72
% 0.18/0.42  # Backward-rewritten                   : 35
% 0.18/0.42  # Generated clauses                    : 545
% 0.18/0.42  # ...of the previous two non-trivial   : 529
% 0.18/0.42  # Contextual simplify-reflections      : 107
% 0.18/0.42  # Paramodulations                      : 541
% 0.18/0.42  # Factorizations                       : 0
% 0.18/0.42  # Equation resolutions                 : 7
% 0.18/0.42  # Propositional unsat checks           : 0
% 0.18/0.42  #    Propositional check models        : 0
% 0.18/0.42  #    Propositional check unsatisfiable : 0
% 0.18/0.42  #    Propositional clauses             : 0
% 0.18/0.42  #    Propositional clauses after purity: 0
% 0.18/0.42  #    Propositional unsat core size     : 0
% 0.18/0.42  #    Propositional preprocessing time  : 0.000
% 0.18/0.42  #    Propositional encoding time       : 0.000
% 0.18/0.42  #    Propositional solver time         : 0.000
% 0.18/0.42  #    Success case prop preproc time    : 0.000
% 0.18/0.42  #    Success case prop encoding time   : 0.000
% 0.18/0.42  #    Success case prop solver time     : 0.000
% 0.18/0.42  # Current number of processed clauses  : 159
% 0.18/0.42  #    Positive orientable unit clauses  : 25
% 0.18/0.42  #    Positive unorientable unit clauses: 0
% 0.18/0.42  #    Negative unit clauses             : 5
% 0.18/0.42  #    Non-unit-clauses                  : 129
% 0.18/0.42  # Current number of unprocessed clauses: 160
% 0.18/0.42  # ...number of literals in the above   : 954
% 0.18/0.42  # Current number of archived formulas  : 0
% 0.18/0.42  # Current number of archived clauses   : 142
% 0.18/0.42  # Clause-clause subsumption calls (NU) : 11506
% 0.18/0.42  # Rec. Clause-clause subsumption calls : 4185
% 0.18/0.42  # Non-unit clause-clause subsumptions  : 270
% 0.18/0.42  # Unit Clause-clause subsumption calls : 469
% 0.18/0.42  # Rewrite failures with RHS unbound    : 0
% 0.18/0.42  # BW rewrite match attempts            : 93
% 0.18/0.42  # BW rewrite match successes           : 8
% 0.18/0.42  # Condensation attempts                : 0
% 0.18/0.42  # Condensation successes               : 0
% 0.18/0.42  # Termbank termtop insertions          : 37821
% 0.18/0.42  
% 0.18/0.42  # -------------------------------------------------
% 0.18/0.42  # User time                : 0.079 s
% 0.18/0.42  # System time              : 0.004 s
% 0.18/0.42  # Total time               : 0.083 s
% 0.18/0.42  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
