%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1821+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:50 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  138 (23767 expanded)
%              Number of clauses        :  115 (6995 expanded)
%              Number of leaves         :   10 (5806 expanded)
%              Depth                    :   26
%              Number of atoms          : 1653 (956089 expanded)
%              Number of equality atoms :   11 (15640 expanded)
%              Maximal formula depth    :   46 (  10 average)
%              Maximal clause size      :  254 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t132_tmap_1,axiom,(
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
                     => ( ( X1 = k1_tsep_1(X1,X4,X5)
                          & r4_tsep_1(X1,X4,X5) )
                       => ( ( v1_funct_1(X3)
                            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                            & v5_pre_topc(X3,X1,X2)
                            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                        <=> ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
                            & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
                            & v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
                            & v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_tmap_1)).

fof(t137_tmap_1,conjecture,(
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
             => ( X1 = k1_tsep_1(X1,X2,X3)
               => ( r3_tsep_1(X1,X2,X3)
                <=> ( r1_tsep_1(X2,X3)
                    & ! [X4] :
                        ( ( ~ v2_struct_0(X4)
                          & v2_pre_topc(X4)
                          & l1_pre_topc(X4) )
                       => ! [X5] :
                            ( ( v1_funct_1(X5)
                              & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
                              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) )
                           => ( ( v1_funct_1(k2_tmap_1(X1,X4,X5,X2))
                                & v1_funct_2(k2_tmap_1(X1,X4,X5,X2),u1_struct_0(X2),u1_struct_0(X4))
                                & v5_pre_topc(k2_tmap_1(X1,X4,X5,X2),X2,X4)
                                & m1_subset_1(k2_tmap_1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
                                & v1_funct_1(k2_tmap_1(X1,X4,X5,X3))
                                & v1_funct_2(k2_tmap_1(X1,X4,X5,X3),u1_struct_0(X3),u1_struct_0(X4))
                                & v5_pre_topc(k2_tmap_1(X1,X4,X5,X3),X3,X4)
                                & m1_subset_1(k2_tmap_1(X1,X4,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) )
                             => ( v1_funct_1(X5)
                                & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
                                & v5_pre_topc(X5,X1,X4)
                                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_tmap_1)).

fof(t85_tsep_1,axiom,(
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
             => ( ( r1_tsep_1(X2,X3)
                  & r4_tsep_1(X1,X2,X3) )
              <=> r3_tsep_1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tsep_1)).

fof(t68_tsep_1,axiom,(
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
             => ( r3_tsep_1(X1,X2,X3)
               => r1_tsep_1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tsep_1)).

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(t136_tmap_1,axiom,(
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
             => ( r3_tsep_1(X1,X2,X3)
              <=> ( r1_tsep_1(X2,X3)
                  & ! [X4] :
                      ( ( ~ v2_struct_0(X4)
                        & v2_pre_topc(X4)
                        & l1_pre_topc(X4) )
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) )
                         => ( ( v1_funct_1(k2_tmap_1(X1,X4,X5,X2))
                              & v1_funct_2(k2_tmap_1(X1,X4,X5,X2),u1_struct_0(X2),u1_struct_0(X4))
                              & v5_pre_topc(k2_tmap_1(X1,X4,X5,X2),X2,X4)
                              & m1_subset_1(k2_tmap_1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
                              & v1_funct_1(k2_tmap_1(X1,X4,X5,X3))
                              & v1_funct_2(k2_tmap_1(X1,X4,X5,X3),u1_struct_0(X3),u1_struct_0(X4))
                              & v5_pre_topc(k2_tmap_1(X1,X4,X5,X3),X3,X4)
                              & m1_subset_1(k2_tmap_1(X1,X4,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) )
                           => ( v1_funct_1(k2_tmap_1(X1,X4,X5,k1_tsep_1(X1,X2,X3)))
                              & v1_funct_2(k2_tmap_1(X1,X4,X5,k1_tsep_1(X1,X2,X3)),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
                              & v5_pre_topc(k2_tmap_1(X1,X4,X5,k1_tsep_1(X1,X2,X3)),k1_tsep_1(X1,X2,X3),X4)
                              & m1_subset_1(k2_tmap_1(X1,X4,X5,k1_tsep_1(X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_tmap_1)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(c_0_9,plain,(
    ! [X1,X5,X4,X3,X2] :
      ( epred1_5(X2,X4,X5,X3,X1)
    <=> ( ( v1_funct_1(X3)
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
          & v5_pre_topc(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
          & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
          & v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
          & v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ),
    introduced(definition)).

fof(c_0_10,axiom,(
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
                     => ( ( X1 = k1_tsep_1(X1,X4,X5)
                          & r4_tsep_1(X1,X4,X5) )
                       => epred1_5(X2,X4,X5,X3,X1) ) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t132_tmap_1,c_0_9])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( X1 = k1_tsep_1(X1,X2,X3)
                 => ( r3_tsep_1(X1,X2,X3)
                  <=> ( r1_tsep_1(X2,X3)
                      & ! [X4] :
                          ( ( ~ v2_struct_0(X4)
                            & v2_pre_topc(X4)
                            & l1_pre_topc(X4) )
                         => ! [X5] :
                              ( ( v1_funct_1(X5)
                                & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
                                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) )
                             => ( ( v1_funct_1(k2_tmap_1(X1,X4,X5,X2))
                                  & v1_funct_2(k2_tmap_1(X1,X4,X5,X2),u1_struct_0(X2),u1_struct_0(X4))
                                  & v5_pre_topc(k2_tmap_1(X1,X4,X5,X2),X2,X4)
                                  & m1_subset_1(k2_tmap_1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
                                  & v1_funct_1(k2_tmap_1(X1,X4,X5,X3))
                                  & v1_funct_2(k2_tmap_1(X1,X4,X5,X3),u1_struct_0(X3),u1_struct_0(X4))
                                  & v5_pre_topc(k2_tmap_1(X1,X4,X5,X3),X3,X4)
                                  & m1_subset_1(k2_tmap_1(X1,X4,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) )
                               => ( v1_funct_1(X5)
                                  & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
                                  & v5_pre_topc(X5,X1,X4)
                                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t137_tmap_1])).

fof(c_0_12,plain,(
    ! [X1,X5,X4,X3,X2] :
      ( epred1_5(X2,X4,X5,X3,X1)
     => ( ( v1_funct_1(X3)
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
          & v5_pre_topc(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
          & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
          & v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
          & v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ v1_funct_1(X26)
      | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X25))
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X25))))
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X27,X24)
      | v2_struct_0(X28)
      | ~ m1_pre_topc(X28,X24)
      | X24 != k1_tsep_1(X24,X27,X28)
      | ~ r4_tsep_1(X24,X27,X28)
      | epred1_5(X25,X27,X28,X26,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_14,plain,(
    ! [X39,X40,X41] :
      ( ( ~ r1_tsep_1(X40,X41)
        | ~ r4_tsep_1(X39,X40,X41)
        | r3_tsep_1(X39,X40,X41)
        | v2_struct_0(X41)
        | ~ m1_pre_topc(X41,X39)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X39)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( r1_tsep_1(X40,X41)
        | ~ r3_tsep_1(X39,X40,X41)
        | v2_struct_0(X41)
        | ~ m1_pre_topc(X41,X39)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X39)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( r4_tsep_1(X39,X40,X41)
        | ~ r3_tsep_1(X39,X40,X41)
        | v2_struct_0(X41)
        | ~ m1_pre_topc(X41,X39)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X39)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t85_tsep_1])])])])])).

fof(c_0_15,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | v2_struct_0(X37)
      | ~ m1_pre_topc(X37,X36)
      | v2_struct_0(X38)
      | ~ m1_pre_topc(X38,X36)
      | ~ r3_tsep_1(X36,X37,X38)
      | r1_tsep_1(X37,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t68_tsep_1])])])])).

fof(c_0_16,negated_conjecture,(
    ! [X47,X48] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & ~ v2_struct_0(esk5_0)
      & m1_pre_topc(esk5_0,esk3_0)
      & esk3_0 = k1_tsep_1(esk3_0,esk4_0,esk5_0)
      & ( ~ v2_struct_0(esk6_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v2_pre_topc(esk6_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( l1_pre_topc(esk6_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_1(esk7_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk6_0))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0))))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk6_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk6_0))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),esk5_0,esk6_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( ~ v1_funct_1(esk7_0)
        | ~ v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk6_0))
        | ~ v5_pre_topc(esk7_0,esk3_0,esk6_0)
        | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0))))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( r1_tsep_1(esk4_0,esk5_0)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_1(X48)
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X47,X48,esk4_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X47,X48,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X47))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X47,X48,esk4_0),esk4_0,X47)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X47,X48,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X47))))
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X47,X48,esk5_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X47,X48,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X47))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X47,X48,esk5_0),esk5_0,X47)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X47,X48,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X47))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(esk3_0),u1_struct_0(X47))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X47))))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_2(X48,u1_struct_0(esk3_0),u1_struct_0(X47))
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X47,X48,esk4_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X47,X48,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X47))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X47,X48,esk4_0),esk4_0,X47)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X47,X48,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X47))))
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X47,X48,esk5_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X47,X48,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X47))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X47,X48,esk5_0),esk5_0,X47)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X47,X48,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X47))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(esk3_0),u1_struct_0(X47))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X47))))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v5_pre_topc(X48,esk3_0,X47)
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X47,X48,esk4_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X47,X48,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X47))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X47,X48,esk4_0),esk4_0,X47)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X47,X48,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X47))))
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X47,X48,esk5_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X47,X48,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X47))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X47,X48,esk5_0),esk5_0,X47)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X47,X48,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X47))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(esk3_0),u1_struct_0(X47))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X47))))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X47))))
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X47,X48,esk4_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X47,X48,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X47))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X47,X48,esk4_0),esk4_0,X47)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X47,X48,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X47))))
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X47,X48,esk5_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X47,X48,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X47))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X47,X48,esk5_0),esk5_0,X47)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X47,X48,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X47))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(esk3_0),u1_struct_0(X47))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X47))))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).

fof(c_0_17,plain,(
    ! [X49,X50,X51,X52,X53] :
      ( ( v1_funct_1(k2_tmap_1(X49,X53,X52,X51))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X49),u1_struct_0(X53))
        | ~ v5_pre_topc(X52,X49,X53)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X53))))
        | ~ epred1_5(X53,X51,X50,X52,X49) )
      & ( v1_funct_2(k2_tmap_1(X49,X53,X52,X51),u1_struct_0(X51),u1_struct_0(X53))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X49),u1_struct_0(X53))
        | ~ v5_pre_topc(X52,X49,X53)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X53))))
        | ~ epred1_5(X53,X51,X50,X52,X49) )
      & ( v5_pre_topc(k2_tmap_1(X49,X53,X52,X51),X51,X53)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X49),u1_struct_0(X53))
        | ~ v5_pre_topc(X52,X49,X53)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X53))))
        | ~ epred1_5(X53,X51,X50,X52,X49) )
      & ( m1_subset_1(k2_tmap_1(X49,X53,X52,X51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X53))))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X49),u1_struct_0(X53))
        | ~ v5_pre_topc(X52,X49,X53)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X53))))
        | ~ epred1_5(X53,X51,X50,X52,X49) )
      & ( v1_funct_1(k2_tmap_1(X49,X53,X52,X50))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X49),u1_struct_0(X53))
        | ~ v5_pre_topc(X52,X49,X53)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X53))))
        | ~ epred1_5(X53,X51,X50,X52,X49) )
      & ( v1_funct_2(k2_tmap_1(X49,X53,X52,X50),u1_struct_0(X50),u1_struct_0(X53))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X49),u1_struct_0(X53))
        | ~ v5_pre_topc(X52,X49,X53)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X53))))
        | ~ epred1_5(X53,X51,X50,X52,X49) )
      & ( v5_pre_topc(k2_tmap_1(X49,X53,X52,X50),X50,X53)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X49),u1_struct_0(X53))
        | ~ v5_pre_topc(X52,X49,X53)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X53))))
        | ~ epred1_5(X53,X51,X50,X52,X49) )
      & ( m1_subset_1(k2_tmap_1(X49,X53,X52,X50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X53))))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X49),u1_struct_0(X53))
        | ~ v5_pre_topc(X52,X49,X53)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X53))))
        | ~ epred1_5(X53,X51,X50,X52,X49) )
      & ( v1_funct_1(X52)
        | ~ v1_funct_1(k2_tmap_1(X49,X53,X52,X51))
        | ~ v1_funct_2(k2_tmap_1(X49,X53,X52,X51),u1_struct_0(X51),u1_struct_0(X53))
        | ~ v5_pre_topc(k2_tmap_1(X49,X53,X52,X51),X51,X53)
        | ~ m1_subset_1(k2_tmap_1(X49,X53,X52,X51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X53))))
        | ~ v1_funct_1(k2_tmap_1(X49,X53,X52,X50))
        | ~ v1_funct_2(k2_tmap_1(X49,X53,X52,X50),u1_struct_0(X50),u1_struct_0(X53))
        | ~ v5_pre_topc(k2_tmap_1(X49,X53,X52,X50),X50,X53)
        | ~ m1_subset_1(k2_tmap_1(X49,X53,X52,X50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X53))))
        | ~ epred1_5(X53,X51,X50,X52,X49) )
      & ( v1_funct_2(X52,u1_struct_0(X49),u1_struct_0(X53))
        | ~ v1_funct_1(k2_tmap_1(X49,X53,X52,X51))
        | ~ v1_funct_2(k2_tmap_1(X49,X53,X52,X51),u1_struct_0(X51),u1_struct_0(X53))
        | ~ v5_pre_topc(k2_tmap_1(X49,X53,X52,X51),X51,X53)
        | ~ m1_subset_1(k2_tmap_1(X49,X53,X52,X51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X53))))
        | ~ v1_funct_1(k2_tmap_1(X49,X53,X52,X50))
        | ~ v1_funct_2(k2_tmap_1(X49,X53,X52,X50),u1_struct_0(X50),u1_struct_0(X53))
        | ~ v5_pre_topc(k2_tmap_1(X49,X53,X52,X50),X50,X53)
        | ~ m1_subset_1(k2_tmap_1(X49,X53,X52,X50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X53))))
        | ~ epred1_5(X53,X51,X50,X52,X49) )
      & ( v5_pre_topc(X52,X49,X53)
        | ~ v1_funct_1(k2_tmap_1(X49,X53,X52,X51))
        | ~ v1_funct_2(k2_tmap_1(X49,X53,X52,X51),u1_struct_0(X51),u1_struct_0(X53))
        | ~ v5_pre_topc(k2_tmap_1(X49,X53,X52,X51),X51,X53)
        | ~ m1_subset_1(k2_tmap_1(X49,X53,X52,X51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X53))))
        | ~ v1_funct_1(k2_tmap_1(X49,X53,X52,X50))
        | ~ v1_funct_2(k2_tmap_1(X49,X53,X52,X50),u1_struct_0(X50),u1_struct_0(X53))
        | ~ v5_pre_topc(k2_tmap_1(X49,X53,X52,X50),X50,X53)
        | ~ m1_subset_1(k2_tmap_1(X49,X53,X52,X50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X53))))
        | ~ epred1_5(X53,X51,X50,X52,X49) )
      & ( m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X53))))
        | ~ v1_funct_1(k2_tmap_1(X49,X53,X52,X51))
        | ~ v1_funct_2(k2_tmap_1(X49,X53,X52,X51),u1_struct_0(X51),u1_struct_0(X53))
        | ~ v5_pre_topc(k2_tmap_1(X49,X53,X52,X51),X51,X53)
        | ~ m1_subset_1(k2_tmap_1(X49,X53,X52,X51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X53))))
        | ~ v1_funct_1(k2_tmap_1(X49,X53,X52,X50))
        | ~ v1_funct_2(k2_tmap_1(X49,X53,X52,X50),u1_struct_0(X50),u1_struct_0(X53))
        | ~ v5_pre_topc(k2_tmap_1(X49,X53,X52,X50),X50,X53)
        | ~ m1_subset_1(k2_tmap_1(X49,X53,X52,X50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X53))))
        | ~ epred1_5(X53,X51,X50,X52,X49) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | epred1_5(X2,X4,X5,X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X5,X1)
    | X1 != k1_tsep_1(X1,X4,X5)
    | ~ r4_tsep_1(X1,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r4_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_tsep_1(X1,X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r1_tsep_1(X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ r3_tsep_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk5_0)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_29,plain,(
    ! [X12,X13,X14,X15] :
      ( ( v1_funct_1(k2_tmap_1(X12,X13,X14,X15))
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
        | ~ l1_struct_0(X15) )
      & ( v1_funct_2(k2_tmap_1(X12,X13,X14,X15),u1_struct_0(X15),u1_struct_0(X13))
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
        | ~ l1_struct_0(X15) )
      & ( m1_subset_1(k2_tmap_1(X12,X13,X14,X15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
        | ~ l1_struct_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

fof(c_0_30,plain,(
    ! [X16] :
      ( ~ l1_pre_topc(X16)
      | l1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_31,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v1_funct_1(k2_tmap_1(X2,X3,X1,X4))
    | ~ v1_funct_2(k2_tmap_1(X2,X3,X1,X4),u1_struct_0(X4),u1_struct_0(X3))
    | ~ v5_pre_topc(k2_tmap_1(X2,X3,X1,X4),X4,X3)
    | ~ m1_subset_1(k2_tmap_1(X2,X3,X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
    | ~ v1_funct_1(k2_tmap_1(X2,X3,X1,X5))
    | ~ v1_funct_2(k2_tmap_1(X2,X3,X1,X5),u1_struct_0(X5),u1_struct_0(X3))
    | ~ v5_pre_topc(k2_tmap_1(X2,X3,X1,X5),X5,X3)
    | ~ m1_subset_1(k2_tmap_1(X2,X3,X1,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
    | ~ epred1_5(X3,X4,X5,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
    ( epred1_5(X1,X2,X3,X4,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | k1_tsep_1(X5,X2,X3) != X5
    | ~ r3_tsep_1(X5,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X1))))
    | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X1))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X3,X5)
    | ~ m1_pre_topc(X2,X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),esk5_0,esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk7_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk6_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk6_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( v2_pre_topc(esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_funct_1(esk7_0)
    | ~ v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk6_0))
    | ~ v5_pre_topc(esk7_0,esk3_0,esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,plain,
    ( v5_pre_topc(X1,X2,X3)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | k1_tsep_1(X2,X5,X4) != X2
    | ~ r3_tsep_1(X2,X5,X4)
    | ~ v5_pre_topc(k2_tmap_1(X2,X3,X1,X4),X4,X3)
    | ~ v5_pre_topc(k2_tmap_1(X2,X3,X1,X5),X5,X3)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(k2_tmap_1(X2,X3,X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
    | ~ m1_subset_1(k2_tmap_1(X2,X3,X1,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v1_funct_2(k2_tmap_1(X2,X3,X1,X4),u1_struct_0(X4),u1_struct_0(X3))
    | ~ v1_funct_2(k2_tmap_1(X2,X3,X1,X5),u1_struct_0(X5),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(k2_tmap_1(X2,X3,X1,X4))
    | ~ v1_funct_1(k2_tmap_1(X2,X3,X1,X5))
    | ~ v1_funct_1(X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X5,X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_48,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),esk5_0,esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_49,negated_conjecture,
    ( l1_pre_topc(esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_34])])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_1(esk7_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_34])])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_34])])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk6_0))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_34])])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk6_0))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_34])])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0))))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_34])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_34])])).

cnf(c_0_56,negated_conjecture,
    ( v2_pre_topc(esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_34])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v2_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_34])])).

cnf(c_0_58,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_62,plain,(
    ! [X17,X18,X19,X20] :
      ( ( v1_funct_1(k2_tmap_1(X17,X18,X19,X20))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))
        | ~ v5_pre_topc(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X17) )
      & ( v1_funct_2(k2_tmap_1(X17,X18,X19,X20),u1_struct_0(X20),u1_struct_0(X18))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))
        | ~ v5_pre_topc(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X17) )
      & ( v5_pre_topc(k2_tmap_1(X17,X18,X19,X20),X20,X18)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))
        | ~ v5_pre_topc(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tmap_1])])])])).

fof(c_0_63,plain,(
    ! [X29,X30,X31,X32,X33] :
      ( ( r1_tsep_1(X30,X31)
        | ~ r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v1_funct_1(k2_tmap_1(X29,X32,X33,k1_tsep_1(X29,X30,X31)))
        | ~ v1_funct_1(k2_tmap_1(X29,X32,X33,X30))
        | ~ v1_funct_2(k2_tmap_1(X29,X32,X33,X30),u1_struct_0(X30),u1_struct_0(X32))
        | ~ v5_pre_topc(k2_tmap_1(X29,X32,X33,X30),X30,X32)
        | ~ m1_subset_1(k2_tmap_1(X29,X32,X33,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X32))))
        | ~ v1_funct_1(k2_tmap_1(X29,X32,X33,X31))
        | ~ v1_funct_2(k2_tmap_1(X29,X32,X33,X31),u1_struct_0(X31),u1_struct_0(X32))
        | ~ v5_pre_topc(k2_tmap_1(X29,X32,X33,X31),X31,X32)
        | ~ m1_subset_1(k2_tmap_1(X29,X32,X33,X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X29),u1_struct_0(X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X32))))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32)
        | ~ r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v1_funct_2(k2_tmap_1(X29,X32,X33,k1_tsep_1(X29,X30,X31)),u1_struct_0(k1_tsep_1(X29,X30,X31)),u1_struct_0(X32))
        | ~ v1_funct_1(k2_tmap_1(X29,X32,X33,X30))
        | ~ v1_funct_2(k2_tmap_1(X29,X32,X33,X30),u1_struct_0(X30),u1_struct_0(X32))
        | ~ v5_pre_topc(k2_tmap_1(X29,X32,X33,X30),X30,X32)
        | ~ m1_subset_1(k2_tmap_1(X29,X32,X33,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X32))))
        | ~ v1_funct_1(k2_tmap_1(X29,X32,X33,X31))
        | ~ v1_funct_2(k2_tmap_1(X29,X32,X33,X31),u1_struct_0(X31),u1_struct_0(X32))
        | ~ v5_pre_topc(k2_tmap_1(X29,X32,X33,X31),X31,X32)
        | ~ m1_subset_1(k2_tmap_1(X29,X32,X33,X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X29),u1_struct_0(X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X32))))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32)
        | ~ r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v5_pre_topc(k2_tmap_1(X29,X32,X33,k1_tsep_1(X29,X30,X31)),k1_tsep_1(X29,X30,X31),X32)
        | ~ v1_funct_1(k2_tmap_1(X29,X32,X33,X30))
        | ~ v1_funct_2(k2_tmap_1(X29,X32,X33,X30),u1_struct_0(X30),u1_struct_0(X32))
        | ~ v5_pre_topc(k2_tmap_1(X29,X32,X33,X30),X30,X32)
        | ~ m1_subset_1(k2_tmap_1(X29,X32,X33,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X32))))
        | ~ v1_funct_1(k2_tmap_1(X29,X32,X33,X31))
        | ~ v1_funct_2(k2_tmap_1(X29,X32,X33,X31),u1_struct_0(X31),u1_struct_0(X32))
        | ~ v5_pre_topc(k2_tmap_1(X29,X32,X33,X31),X31,X32)
        | ~ m1_subset_1(k2_tmap_1(X29,X32,X33,X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X29),u1_struct_0(X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X32))))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32)
        | ~ r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_subset_1(k2_tmap_1(X29,X32,X33,k1_tsep_1(X29,X30,X31)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X30,X31)),u1_struct_0(X32))))
        | ~ v1_funct_1(k2_tmap_1(X29,X32,X33,X30))
        | ~ v1_funct_2(k2_tmap_1(X29,X32,X33,X30),u1_struct_0(X30),u1_struct_0(X32))
        | ~ v5_pre_topc(k2_tmap_1(X29,X32,X33,X30),X30,X32)
        | ~ m1_subset_1(k2_tmap_1(X29,X32,X33,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X32))))
        | ~ v1_funct_1(k2_tmap_1(X29,X32,X33,X31))
        | ~ v1_funct_2(k2_tmap_1(X29,X32,X33,X31),u1_struct_0(X31),u1_struct_0(X32))
        | ~ v5_pre_topc(k2_tmap_1(X29,X32,X33,X31),X31,X32)
        | ~ m1_subset_1(k2_tmap_1(X29,X32,X33,X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X29),u1_struct_0(X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X32))))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32)
        | ~ r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( ~ v2_struct_0(esk1_3(X29,X30,X31))
        | ~ r1_tsep_1(X30,X31)
        | r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v2_pre_topc(esk1_3(X29,X30,X31))
        | ~ r1_tsep_1(X30,X31)
        | r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( l1_pre_topc(esk1_3(X29,X30,X31))
        | ~ r1_tsep_1(X30,X31)
        | r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v1_funct_1(esk2_3(X29,X30,X31))
        | ~ r1_tsep_1(X30,X31)
        | r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v1_funct_2(esk2_3(X29,X30,X31),u1_struct_0(X29),u1_struct_0(esk1_3(X29,X30,X31)))
        | ~ r1_tsep_1(X30,X31)
        | r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_subset_1(esk2_3(X29,X30,X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(esk1_3(X29,X30,X31)))))
        | ~ r1_tsep_1(X30,X31)
        | r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v1_funct_1(k2_tmap_1(X29,esk1_3(X29,X30,X31),esk2_3(X29,X30,X31),X30))
        | ~ r1_tsep_1(X30,X31)
        | r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v1_funct_2(k2_tmap_1(X29,esk1_3(X29,X30,X31),esk2_3(X29,X30,X31),X30),u1_struct_0(X30),u1_struct_0(esk1_3(X29,X30,X31)))
        | ~ r1_tsep_1(X30,X31)
        | r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v5_pre_topc(k2_tmap_1(X29,esk1_3(X29,X30,X31),esk2_3(X29,X30,X31),X30),X30,esk1_3(X29,X30,X31))
        | ~ r1_tsep_1(X30,X31)
        | r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_subset_1(k2_tmap_1(X29,esk1_3(X29,X30,X31),esk2_3(X29,X30,X31),X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(esk1_3(X29,X30,X31)))))
        | ~ r1_tsep_1(X30,X31)
        | r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v1_funct_1(k2_tmap_1(X29,esk1_3(X29,X30,X31),esk2_3(X29,X30,X31),X31))
        | ~ r1_tsep_1(X30,X31)
        | r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v1_funct_2(k2_tmap_1(X29,esk1_3(X29,X30,X31),esk2_3(X29,X30,X31),X31),u1_struct_0(X31),u1_struct_0(esk1_3(X29,X30,X31)))
        | ~ r1_tsep_1(X30,X31)
        | r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( v5_pre_topc(k2_tmap_1(X29,esk1_3(X29,X30,X31),esk2_3(X29,X30,X31),X31),X31,esk1_3(X29,X30,X31))
        | ~ r1_tsep_1(X30,X31)
        | r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_subset_1(k2_tmap_1(X29,esk1_3(X29,X30,X31),esk2_3(X29,X30,X31),X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(esk1_3(X29,X30,X31)))))
        | ~ r1_tsep_1(X30,X31)
        | r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( ~ v1_funct_1(k2_tmap_1(X29,esk1_3(X29,X30,X31),esk2_3(X29,X30,X31),k1_tsep_1(X29,X30,X31)))
        | ~ v1_funct_2(k2_tmap_1(X29,esk1_3(X29,X30,X31),esk2_3(X29,X30,X31),k1_tsep_1(X29,X30,X31)),u1_struct_0(k1_tsep_1(X29,X30,X31)),u1_struct_0(esk1_3(X29,X30,X31)))
        | ~ v5_pre_topc(k2_tmap_1(X29,esk1_3(X29,X30,X31),esk2_3(X29,X30,X31),k1_tsep_1(X29,X30,X31)),k1_tsep_1(X29,X30,X31),esk1_3(X29,X30,X31))
        | ~ m1_subset_1(k2_tmap_1(X29,esk1_3(X29,X30,X31),esk2_3(X29,X30,X31),k1_tsep_1(X29,X30,X31)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X29,X30,X31)),u1_struct_0(esk1_3(X29,X30,X31)))))
        | ~ r1_tsep_1(X30,X31)
        | r3_tsep_1(X29,X30,X31)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t136_tmap_1])])])])])])).

cnf(c_0_64,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X4) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(esk7_0,esk3_0,esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_46,c_0_36]),c_0_38])).

cnf(c_0_66,negated_conjecture,
    ( v5_pre_topc(esk7_0,esk3_0,esk6_0)
    | v2_struct_0(X1)
    | k1_tsep_1(esk3_0,X1,esk5_0) != esk3_0
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,X1,esk5_0)
    | ~ v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,X1),X1,esk6_0)
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk6_0))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,X1),u1_struct_0(X1),u1_struct_0(esk6_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,X1))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_22]),c_0_23]),c_0_25])]),c_0_26]),c_0_28]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_34])])).

cnf(c_0_68,negated_conjecture,
    ( esk3_0 = k1_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_34])])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_34])])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_34])])).

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
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_73,plain,
    ( v2_pre_topc(esk1_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,plain,
    ( l1_pre_topc(esk1_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,plain,
    ( r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk1_3(X1,X2,X3))
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_76,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_45])).

cnf(c_0_77,negated_conjecture,
    ( v5_pre_topc(X1,esk3_0,X2)
    | v2_struct_0(X2)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v1_funct_1(k2_tmap_1(esk3_0,X2,X1,esk4_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,X2,X1,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(esk3_0,X2,X1,esk4_0),esk4_0,X2)
    | ~ m1_subset_1(k2_tmap_1(esk3_0,X2,X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,X2,X1,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,X2,X1,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(esk3_0,X2,X1,esk5_0),esk5_0,X2)
    | ~ m1_subset_1(k2_tmap_1(esk3_0,X2,X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_78,plain,
    ( v5_pre_topc(k2_tmap_1(X1,esk1_3(X1,X2,X3),esk2_3(X1,X2,X3),X3),X3,esk1_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_79,negated_conjecture,
    ( ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(esk7_0,esk3_0,esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_34])])).

cnf(c_0_80,negated_conjecture,
    ( v5_pre_topc(esk7_0,esk3_0,esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_24])]),c_0_27]),c_0_69]),c_0_70]),c_0_71])).

cnf(c_0_81,plain,
    ( r3_tsep_1(X1,X2,X3)
    | v5_pre_topc(k2_tmap_1(X4,esk1_3(X1,X2,X3),X5,X6),X6,esk1_3(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X6)
    | ~ r1_tsep_1(X2,X3)
    | ~ v5_pre_topc(X5,X4,esk1_3(X1,X2,X3))
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(esk1_3(X1,X2,X3)))))
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(esk1_3(X1,X2,X3)))
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X6,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_75])).

fof(c_0_82,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v2_struct_0(k1_tsep_1(X9,X10,X11))
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X9) )
      & ( v1_pre_topc(k1_tsep_1(X9,X10,X11))
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X9) )
      & ( m1_pre_topc(k1_tsep_1(X9,X10,X11),X9)
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

cnf(c_0_83,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_45])).

cnf(c_0_84,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | r3_tsep_1(esk3_0,X1,esk5_0)
    | v5_pre_topc(esk2_3(esk3_0,X1,esk5_0),esk3_0,esk1_3(esk3_0,X1,esk5_0))
    | v2_struct_0(esk1_3(esk3_0,X1,esk5_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk5_0)
    | ~ v5_pre_topc(k2_tmap_1(esk3_0,esk1_3(esk3_0,X1,esk5_0),esk2_3(esk3_0,X1,esk5_0),esk4_0),esk4_0,esk1_3(esk3_0,X1,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,X1,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,X1,esk5_0),esk2_3(esk3_0,X1,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,X1,esk5_0)))))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,X1,esk5_0),esk2_3(esk3_0,X1,esk5_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,X1,esk5_0)))))
    | ~ m1_subset_1(esk2_3(esk3_0,X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,X1,esk5_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,X1,esk5_0),esk2_3(esk3_0,X1,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,X1,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,X1,esk5_0),esk2_3(esk3_0,X1,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,X1,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,X1,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,X1,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,X1,esk5_0),esk2_3(esk3_0,X1,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,X1,esk5_0),esk2_3(esk3_0,X1,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,X1,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,X1,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_22]),c_0_23]),c_0_25])]),c_0_26]),c_0_28])).

cnf(c_0_85,plain,
    ( v5_pre_topc(k2_tmap_1(X1,esk1_3(X1,X2,X3),esk2_3(X1,X2,X3),X2),X2,esk1_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_86,negated_conjecture,
    ( ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_54])).

cnf(c_0_87,plain,
    ( r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k2_tmap_1(X1,esk1_3(X1,X2,X3),esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3)))
    | ~ v1_funct_2(k2_tmap_1(X1,esk1_3(X1,X2,X3),esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3)),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))
    | ~ v5_pre_topc(k2_tmap_1(X1,esk1_3(X1,X2,X3),esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3)),k1_tsep_1(X1,X2,X3),esk1_3(X1,X2,X3))
    | ~ m1_subset_1(k2_tmap_1(X1,esk1_3(X1,X2,X3),esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))))
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_88,negated_conjecture,
    ( r3_tsep_1(X1,X2,X3)
    | v5_pre_topc(k2_tmap_1(esk3_0,esk1_3(X1,X2,X3),X4,X5),X5,esk1_3(X1,X2,X3))
    | v2_struct_0(X5)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ v5_pre_topc(X4,esk3_0,esk1_3(X1,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(X1,X2,X3)))))
    | ~ v1_funct_2(X4,u1_struct_0(esk3_0),u1_struct_0(esk1_3(X1,X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X5,esk3_0)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_22]),c_0_25])]),c_0_28])).

cnf(c_0_89,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_25])).

cnf(c_0_91,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_92,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_34]),c_0_24]),c_0_22]),c_0_23]),c_0_25])]),c_0_27]),c_0_26]),c_0_28]),c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( r3_tsep_1(esk3_0,X1,X2)
    | v2_struct_0(k1_tsep_1(esk3_0,X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X2)
    | ~ v5_pre_topc(esk2_3(esk3_0,X1,X2),esk3_0,esk1_3(esk3_0,X1,X2))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,X1,X2),esk2_3(esk3_0,X1,X2),k1_tsep_1(esk3_0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,X1,X2)),u1_struct_0(esk1_3(esk3_0,X1,X2)))))
    | ~ m1_subset_1(esk2_3(esk3_0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,X1,X2)))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,X1,X2),esk2_3(esk3_0,X1,X2),k1_tsep_1(esk3_0,X1,X2)),u1_struct_0(k1_tsep_1(esk3_0,X1,X2)),u1_struct_0(esk1_3(esk3_0,X1,X2)))
    | ~ v1_funct_2(esk2_3(esk3_0,X1,X2),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,X1,X2)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,X1,X2),esk2_3(esk3_0,X1,X2),k1_tsep_1(esk3_0,X1,X2)))
    | ~ v1_funct_1(esk2_3(esk3_0,X1,X2))
    | ~ m1_pre_topc(k1_tsep_1(esk3_0,X1,X2),esk3_0)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_22]),c_0_25])]),c_0_28])).

cnf(c_0_94,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_68]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_95,negated_conjecture,
    ( r3_tsep_1(X1,X2,X3)
    | m1_subset_1(k2_tmap_1(X4,esk1_3(X1,X2,X3),X5,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(X1,X2,X3)))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(esk1_3(X1,X2,X3)))))
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(esk1_3(X1,X2,X3)))
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_74])).

cnf(c_0_96,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1),u1_struct_0(X1),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_22]),c_0_25])]),c_0_28])).

cnf(c_0_97,plain,
    ( m1_subset_1(k2_tmap_1(X1,esk1_3(X1,X2,X3),esk2_3(X1,X2,X3),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(esk1_3(X1,X2,X3)))))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_98,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_99,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk3_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_92]),c_0_68]),c_0_34]),c_0_68]),c_0_68]),c_0_68]),c_0_68]),c_0_68]),c_0_68]),c_0_94]),c_0_23]),c_0_24])]),c_0_86]),c_0_28]),c_0_27]),c_0_26])).

cnf(c_0_100,negated_conjecture,
    ( r3_tsep_1(X1,X2,X3)
    | m1_subset_1(k2_tmap_1(esk3_0,esk1_3(X1,X2,X3),X4,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(X1,X2,X3)))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(X1,X2,X3)))))
    | ~ v1_funct_2(X4,u1_struct_0(esk3_0),u1_struct_0(esk1_3(X1,X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_25])).

cnf(c_0_101,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1),u1_struct_0(X1),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_102,plain,
    ( m1_subset_1(k2_tmap_1(X1,esk1_3(X1,X2,X3),esk2_3(X1,X2,X3),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_103,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_92]),c_0_22]),c_0_25])]),c_0_28])).

cnf(c_0_104,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk3_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_105,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1),u1_struct_0(X1),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_106,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk1_3(X1,X2,X3)))))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_107,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_97]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_108,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk3_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_97]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_109,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1),u1_struct_0(X1),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_110,plain,
    ( v1_funct_2(k2_tmap_1(X1,esk1_3(X1,X2,X3),esk2_3(X1,X2,X3),X3),u1_struct_0(X3),u1_struct_0(esk1_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_111,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_102]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_112,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk3_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_102]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_113,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1),u1_struct_0(X1),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_114,plain,
    ( v1_funct_2(k2_tmap_1(X1,esk1_3(X1,X2,X3),esk2_3(X1,X2,X3),X2),u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_115,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_106]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_116,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk3_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_106]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_117,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1),u1_struct_0(X1),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_118,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_110]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_119,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk3_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_94])]),c_0_28])).

cnf(c_0_120,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_114]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_121,plain,
    ( v1_funct_2(esk2_3(X1,X2,X3),u1_struct_0(X1),u1_struct_0(esk1_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_122,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk3_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_110]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_123,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_124,plain,
    ( v1_funct_1(k2_tmap_1(X1,esk1_3(X1,X2,X3),esk2_3(X1,X2,X3),X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_125,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk3_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_114]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_126,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_127,plain,
    ( v1_funct_1(k2_tmap_1(X1,esk1_3(X1,X2,X3),esk2_3(X1,X2,X3),X2))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_128,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk3_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_121]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_129,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_130,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_94])]),c_0_28])).

cnf(c_0_131,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_124]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_132,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_127]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_133,plain,
    ( v1_funct_1(esk2_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_134,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_135,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_73]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_136,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_74]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_137,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_136]),c_0_34]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_86]),c_0_26]),c_0_27]),c_0_28]),
    [proof]).

%------------------------------------------------------------------------------
