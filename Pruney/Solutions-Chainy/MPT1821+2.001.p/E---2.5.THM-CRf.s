%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:34 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  146 (634384 expanded)
%              Number of clauses        :  135 (186228 expanded)
%              Number of leaves         :    5 (155724 expanded)
%              Depth                    :   17
%              Number of atoms          : 1074 (29618248 expanded)
%              Number of equality atoms :   25 (420739 expanded)
%              Maximal formula depth    :   46 (   6 average)
%              Maximal clause size      :  254 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t135_tmap_1,axiom,(
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
                            & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) )
                         => ( ( v1_funct_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5))
                              & v1_funct_2(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),u1_struct_0(X2),u1_struct_0(X4))
                              & v5_pre_topc(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),X2,X4)
                              & m1_subset_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
                              & v1_funct_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5))
                              & v1_funct_2(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),u1_struct_0(X3),u1_struct_0(X4))
                              & v5_pre_topc(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),X3,X4)
                              & m1_subset_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) )
                           => ( v1_funct_1(X5)
                              & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
                              & v5_pre_topc(X5,k1_tsep_1(X1,X2,X3),X4)
                              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_tmap_1)).

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

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( r1_tsep_1(X16,X17)
        | ~ r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v1_funct_1(X19)
        | ~ v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19))
        | ~ v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),u1_struct_0(X16),u1_struct_0(X18))
        | ~ v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),X16,X18)
        | ~ m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X18))))
        | ~ v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19))
        | ~ v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),u1_struct_0(X17),u1_struct_0(X18))
        | ~ v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),X17,X18)
        | ~ m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v1_funct_2(X19,u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))
        | ~ v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19))
        | ~ v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),u1_struct_0(X16),u1_struct_0(X18))
        | ~ v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),X16,X18)
        | ~ m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X18))))
        | ~ v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19))
        | ~ v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),u1_struct_0(X17),u1_struct_0(X18))
        | ~ v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),X17,X18)
        | ~ m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v5_pre_topc(X19,k1_tsep_1(X15,X16,X17),X18)
        | ~ v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19))
        | ~ v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),u1_struct_0(X16),u1_struct_0(X18))
        | ~ v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),X16,X18)
        | ~ m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X18))))
        | ~ v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19))
        | ~ v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),u1_struct_0(X17),u1_struct_0(X18))
        | ~ v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),X17,X18)
        | ~ m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))))
        | ~ v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19))
        | ~ v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),u1_struct_0(X16),u1_struct_0(X18))
        | ~ v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),X16,X18)
        | ~ m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X18))))
        | ~ v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19))
        | ~ v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),u1_struct_0(X17),u1_struct_0(X18))
        | ~ v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),X17,X18)
        | ~ m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ v2_struct_0(esk1_3(X15,X16,X17))
        | ~ r1_tsep_1(X16,X17)
        | r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v2_pre_topc(esk1_3(X15,X16,X17))
        | ~ r1_tsep_1(X16,X17)
        | r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( l1_pre_topc(esk1_3(X15,X16,X17))
        | ~ r1_tsep_1(X16,X17)
        | r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v1_funct_1(esk2_3(X15,X16,X17))
        | ~ r1_tsep_1(X16,X17)
        | r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v1_funct_2(esk2_3(X15,X16,X17),u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(esk1_3(X15,X16,X17)))
        | ~ r1_tsep_1(X16,X17)
        | r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk2_3(X15,X16,X17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(esk1_3(X15,X16,X17)))))
        | ~ r1_tsep_1(X16,X17)
        | r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v1_funct_1(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X16,esk2_3(X15,X16,X17)))
        | ~ r1_tsep_1(X16,X17)
        | r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v1_funct_2(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X16,esk2_3(X15,X16,X17)),u1_struct_0(X16),u1_struct_0(esk1_3(X15,X16,X17)))
        | ~ r1_tsep_1(X16,X17)
        | r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v5_pre_topc(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X16,esk2_3(X15,X16,X17)),X16,esk1_3(X15,X16,X17))
        | ~ r1_tsep_1(X16,X17)
        | r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X16,esk2_3(X15,X16,X17)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(esk1_3(X15,X16,X17)))))
        | ~ r1_tsep_1(X16,X17)
        | r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v1_funct_1(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X17,esk2_3(X15,X16,X17)))
        | ~ r1_tsep_1(X16,X17)
        | r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v1_funct_2(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X17,esk2_3(X15,X16,X17)),u1_struct_0(X17),u1_struct_0(esk1_3(X15,X16,X17)))
        | ~ r1_tsep_1(X16,X17)
        | r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v5_pre_topc(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X17,esk2_3(X15,X16,X17)),X17,esk1_3(X15,X16,X17))
        | ~ r1_tsep_1(X16,X17)
        | r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X17,esk2_3(X15,X16,X17)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(esk1_3(X15,X16,X17)))))
        | ~ r1_tsep_1(X16,X17)
        | r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ v1_funct_1(esk2_3(X15,X16,X17))
        | ~ v1_funct_2(esk2_3(X15,X16,X17),u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(esk1_3(X15,X16,X17)))
        | ~ v5_pre_topc(esk2_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),esk1_3(X15,X16,X17))
        | ~ m1_subset_1(esk2_3(X15,X16,X17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(esk1_3(X15,X16,X17)))))
        | ~ r1_tsep_1(X16,X17)
        | r3_tsep_1(X15,X16,X17)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t135_tmap_1])])])])])])).

fof(c_0_7,negated_conjecture,(
    ! [X28,X29] :
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
      & ( v1_funct_1(X29)
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk4_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X28))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk4_0),esk4_0,X28)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X28))))
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk5_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X28))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk5_0),esk5_0,X28)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X28))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(esk3_0),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X28))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_2(X29,u1_struct_0(esk3_0),u1_struct_0(X28))
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk4_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X28))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk4_0),esk4_0,X28)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X28))))
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk5_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X28))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk5_0),esk5_0,X28)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X28))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(esk3_0),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X28))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v5_pre_topc(X29,esk3_0,X28)
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk4_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X28))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk4_0),esk4_0,X28)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X28))))
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk5_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X28))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk5_0),esk5_0,X28)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X28))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(esk3_0),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X28))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X28))))
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk4_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X28))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk4_0),esk4_0,X28)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X28))))
        | ~ v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk5_0))
        | ~ v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X28))
        | ~ v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk5_0),esk5_0,X28)
        | ~ m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X28))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(esk3_0),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X28))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])])).

cnf(c_0_8,plain,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r3_tsep_1(X3,X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk5_0)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( v1_funct_2(esk2_3(X1,X2,X3),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_19,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_23,plain,(
    ! [X6,X7,X8,X9] :
      ( v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ m1_pre_topc(X9,X6)
      | k2_tmap_1(X6,X7,X8,X9) = k2_partfun1(u1_struct_0(X6),u1_struct_0(X7),X8,u1_struct_0(X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_24,negated_conjecture,
    ( r3_tsep_1(X1,esk4_0,esk5_0)
    | v1_funct_2(esk2_3(X1,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(X1,esk4_0,esk5_0)),u1_struct_0(esk1_3(X1,esk4_0,esk5_0)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_15]),c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( esk3_0 = k1_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( r3_tsep_1(X1,esk4_0,esk5_0)
    | v2_pre_topc(esk1_3(X1,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_18]),c_0_15]),c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( r3_tsep_1(X1,esk4_0,esk5_0)
    | l1_pre_topc(esk1_3(X1,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_18]),c_0_15]),c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( r3_tsep_1(X1,esk4_0,esk5_0)
    | v1_funct_1(esk2_3(X1,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_15]),c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( r3_tsep_1(X1,esk4_0,esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_struct_0(esk1_3(X1,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_15]),c_0_16])).

cnf(c_0_30,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_10]),c_0_25]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( r3_tsep_1(X1,esk4_0,esk5_0)
    | m1_subset_1(esk2_3(X1,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk4_0,esk5_0)),u1_struct_0(esk1_3(X1,esk4_0,esk5_0)))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_18]),c_0_15]),c_0_16])).

fof(c_0_38,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(X12,X10)
      | ~ m1_pre_topc(X13,X10)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X11))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X11))))
      | ~ m1_pre_topc(X13,X12)
      | k3_tmap_1(X10,X11,X12,X13,X14) = k2_partfun1(u1_struct_0(X12),u1_struct_0(X11),X14,u1_struct_0(X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_39,plain,(
    ! [X22] :
      ( ~ l1_pre_topc(X22)
      | m1_pre_topc(X22,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_40,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)),esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_12]),c_0_13])]),c_0_14]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_10]),c_0_25]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_42,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),X2,esk1_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_45,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)),esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k3_tmap_1(X1,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,X2,esk2_3(esk3_0,esk4_0,esk5_0)) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)),esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(X2))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_41]),c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_12])).

cnf(c_0_48,plain,
    ( v1_funct_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_49,plain,
    ( v1_funct_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_50,plain,
    ( v1_funct_2(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),u1_struct_0(X3),u1_struct_0(esk1_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_51,plain,
    ( v1_funct_2(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_52,plain,
    ( m1_subset_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(esk1_3(X1,X2,X3)))))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_53,plain,
    ( m1_subset_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_54,plain,
    ( v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),X3,esk1_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_55,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk4_0,esk2_3(X1,esk4_0,esk5_0)),esk4_0,esk1_3(X1,esk4_0,esk5_0))
    | r3_tsep_1(X1,esk4_0,esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_18]),c_0_15]),c_0_16])).

cnf(c_0_56,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)),esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)) = k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_11])).

cnf(c_0_57,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)),esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0)) = k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_11]),c_0_11]),c_0_47]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_58,negated_conjecture,
    ( r3_tsep_1(X1,esk4_0,esk5_0)
    | v1_funct_1(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk5_0,esk2_3(X1,esk4_0,esk5_0)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_18]),c_0_15]),c_0_16])).

cnf(c_0_59,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)),esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk5_0)) = k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_10])).

cnf(c_0_60,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)),esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk5_0)) = k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_10]),c_0_10]),c_0_47]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_61,negated_conjecture,
    ( r3_tsep_1(X1,esk4_0,esk5_0)
    | v1_funct_1(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk4_0,esk2_3(X1,esk4_0,esk5_0)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_18]),c_0_15]),c_0_16])).

cnf(c_0_62,negated_conjecture,
    ( r3_tsep_1(X1,esk4_0,esk5_0)
    | v1_funct_2(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk5_0,esk2_3(X1,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(X1,esk4_0,esk5_0)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_18]),c_0_15]),c_0_16])).

cnf(c_0_63,negated_conjecture,
    ( r3_tsep_1(X1,esk4_0,esk5_0)
    | v1_funct_2(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk4_0,esk2_3(X1,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(X1,esk4_0,esk5_0)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_18]),c_0_15]),c_0_16])).

cnf(c_0_64,negated_conjecture,
    ( r3_tsep_1(X1,esk4_0,esk5_0)
    | m1_subset_1(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk5_0,esk2_3(X1,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk1_3(X1,esk4_0,esk5_0)))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_18]),c_0_15]),c_0_16])).

cnf(c_0_65,negated_conjecture,
    ( r3_tsep_1(X1,esk4_0,esk5_0)
    | m1_subset_1(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk4_0,esk2_3(X1,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(X1,esk4_0,esk5_0)))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_18]),c_0_15]),c_0_16])).

cnf(c_0_66,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk5_0,esk2_3(X1,esk4_0,esk5_0)),esk5_0,esk1_3(X1,esk4_0,esk5_0))
    | r3_tsep_1(X1,esk4_0,esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_18]),c_0_15]),c_0_16])).

cnf(c_0_67,plain,
    ( r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(esk2_3(X1,X2,X3))
    | ~ v1_funct_2(esk2_3(X1,X2,X3),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))
    | ~ v5_pre_topc(esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),esk1_3(X1,X2,X3))
    | ~ m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))))
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_68,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_10]),c_0_25]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_69,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)) = k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_10]),c_0_25]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_71,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)) = k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_72,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_10]),c_0_25]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_73,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_10]),c_0_25]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_74,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_10]),c_0_25]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_75,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | m1_subset_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_10]),c_0_25]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_76,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | m1_subset_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_10]),c_0_25]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_77,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_10]),c_0_25]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_78,plain,
    ( r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v5_pre_topc(esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),esk1_3(X1,X2,X3))
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_67,c_0_21]),c_0_17]),c_0_30])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk6_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_80,negated_conjecture,
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
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_81,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_82,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_69])).

cnf(c_0_84,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_71])).

cnf(c_0_85,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_69])).

cnf(c_0_86,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_71])).

cnf(c_0_87,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_69])).

cnf(c_0_88,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_71])).

cnf(c_0_89,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0,esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_25]),c_0_18]),c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_15]),c_0_16]),c_0_14])).

cnf(c_0_90,negated_conjecture,
    ( v1_funct_1(esk7_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_91,negated_conjecture,
    ( l1_pre_topc(esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_92,negated_conjecture,
    ( v2_pre_topc(esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_93,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_95,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk6_0))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_18])])).

cnf(c_0_96,negated_conjecture,
    ( r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_33]),c_0_34]),c_0_35]),c_0_82]),c_0_83]),c_0_32]),c_0_84]),c_0_85]),c_0_41]),c_0_86]),c_0_87]),c_0_88]),c_0_36]),c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( v1_funct_1(esk7_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_18])])).

cnf(c_0_98,negated_conjecture,
    ( l1_pre_topc(esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_18])])).

cnf(c_0_99,negated_conjecture,
    ( v2_pre_topc(esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_18])])).

cnf(c_0_100,negated_conjecture,
    ( ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v2_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_18])])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0))))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_18])])).

cnf(c_0_102,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96])])).

cnf(c_0_103,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_96])])).

cnf(c_0_104,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_96])])).

cnf(c_0_105,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_96])])).

cnf(c_0_106,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_96])])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_96])])).

cnf(c_0_108,negated_conjecture,
    ( ~ v1_funct_1(esk7_0)
    | ~ v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk6_0))
    | ~ v5_pre_topc(esk7_0,esk3_0,esk6_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_109,plain,
    ( v5_pre_topc(X1,k1_tsep_1(X2,X3,X4),X5)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1))
    | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),u1_struct_0(X3),u1_struct_0(X5))
    | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),X3,X5)
    | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X5))))
    | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1))
    | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),u1_struct_0(X4),u1_struct_0(X5))
    | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),X4,X5)
    | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(X2,X3,X4)),u1_struct_0(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X4)),u1_struct_0(X5))))
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X5)
    | ~ r3_tsep_1(X2,X3,X4)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_110,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk6_0),esk7_0,u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk6_0,esk7_0,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_102]),c_0_103]),c_0_104]),c_0_12]),c_0_105]),c_0_13])]),c_0_106]),c_0_14]),c_0_107])])).

cnf(c_0_111,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),esk5_0,esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_113,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk6_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_114,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_115,negated_conjecture,
    ( ~ v5_pre_topc(esk7_0,esk3_0,esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_108,c_0_90]),c_0_79])).

cnf(c_0_116,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_118,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_119,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_120,negated_conjecture,
    ( v5_pre_topc(X1,esk3_0,X2)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1),esk5_0,X2)
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1),esk4_0,X2)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ m1_subset_1(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))
    | ~ m1_subset_1(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X2))))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1),u1_struct_0(esk5_0),u1_struct_0(X2))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(X2))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(X2))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_25]),c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_15]),c_0_16]),c_0_14])).

cnf(c_0_121,negated_conjecture,
    ( k3_tmap_1(X1,esk6_0,esk3_0,X2,esk7_0) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk6_0),esk7_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_102]),c_0_103]),c_0_104]),c_0_105])]),c_0_106]),c_0_107])])).

cnf(c_0_122,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk5_0)) = k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_10])).

cnf(c_0_123,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),esk5_0,esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_18])])).

cnf(c_0_124,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_18])])).

cnf(c_0_125,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk6_0))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_18])])).

cnf(c_0_126,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_18])])).

cnf(c_0_127,negated_conjecture,
    ( ~ v5_pre_topc(esk7_0,esk3_0,esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_18])]),c_0_101])).

cnf(c_0_128,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk4_0)) = k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_11])).

cnf(c_0_129,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_18])])).

cnf(c_0_130,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_18])])).

cnf(c_0_131,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_18])])).

cnf(c_0_132,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_18])])).

cnf(c_0_133,negated_conjecture,
    ( v5_pre_topc(X1,esk3_0,X2)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1),esk5_0,X2)
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1),esk4_0,X2)
    | ~ m1_subset_1(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))
    | ~ m1_subset_1(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X2))))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1),u1_struct_0(esk5_0),u1_struct_0(X2))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(X2))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(X2))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_96])])).

cnf(c_0_134,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk6_0,esk3_0,esk5_0,esk7_0) = k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_10]),c_0_122]),c_0_10]),c_0_47]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_135,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_96])])).

cnf(c_0_136,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_96])])).

cnf(c_0_137,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_96])])).

cnf(c_0_138,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_96])])).

cnf(c_0_139,negated_conjecture,
    ( ~ v5_pre_topc(esk7_0,esk3_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_96])])).

cnf(c_0_140,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk6_0,esk3_0,esk4_0,esk7_0) = k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_11]),c_0_128]),c_0_11]),c_0_47]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_141,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_96])])).

cnf(c_0_142,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_96])])).

cnf(c_0_143,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_96])])).

cnf(c_0_144,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_96])])).

cnf(c_0_145,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_135]),c_0_136]),c_0_107]),c_0_137]),c_0_102]),c_0_138]),c_0_103]),c_0_104]),c_0_105])]),c_0_139]),c_0_106]),c_0_140]),c_0_141]),c_0_140]),c_0_142]),c_0_140]),c_0_143]),c_0_140]),c_0_144])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.40  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.031 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t137_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(X1=k1_tsep_1(X1,X2,X3)=>(r3_tsep_1(X1,X2,X3)<=>(r1_tsep_1(X2,X3)&![X4]:(((~(v2_struct_0(X4))&v2_pre_topc(X4))&l1_pre_topc(X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))))=>((((((((v1_funct_1(k2_tmap_1(X1,X4,X5,X2))&v1_funct_2(k2_tmap_1(X1,X4,X5,X2),u1_struct_0(X2),u1_struct_0(X4)))&v5_pre_topc(k2_tmap_1(X1,X4,X5,X2),X2,X4))&m1_subset_1(k2_tmap_1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4)))))&v1_funct_1(k2_tmap_1(X1,X4,X5,X3)))&v1_funct_2(k2_tmap_1(X1,X4,X5,X3),u1_struct_0(X3),u1_struct_0(X4)))&v5_pre_topc(k2_tmap_1(X1,X4,X5,X3),X3,X4))&m1_subset_1(k2_tmap_1(X1,X4,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))))=>(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4)))&v5_pre_topc(X5,X1,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_tmap_1)).
% 0.13/0.40  fof(t135_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r3_tsep_1(X1,X2,X3)<=>(r1_tsep_1(X2,X3)&![X4]:(((~(v2_struct_0(X4))&v2_pre_topc(X4))&l1_pre_topc(X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))))=>((((((((v1_funct_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5))&v1_funct_2(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),u1_struct_0(X2),u1_struct_0(X4)))&v5_pre_topc(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),X2,X4))&m1_subset_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4)))))&v1_funct_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5)))&v1_funct_2(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),u1_struct_0(X3),u1_struct_0(X4)))&v5_pre_topc(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),X3,X4))&m1_subset_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))))=>(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))&v5_pre_topc(X5,k1_tsep_1(X1,X2,X3),X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_tmap_1)).
% 0.13/0.40  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.13/0.40  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.13/0.40  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.13/0.40  fof(c_0_5, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(X1=k1_tsep_1(X1,X2,X3)=>(r3_tsep_1(X1,X2,X3)<=>(r1_tsep_1(X2,X3)&![X4]:(((~(v2_struct_0(X4))&v2_pre_topc(X4))&l1_pre_topc(X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))))=>((((((((v1_funct_1(k2_tmap_1(X1,X4,X5,X2))&v1_funct_2(k2_tmap_1(X1,X4,X5,X2),u1_struct_0(X2),u1_struct_0(X4)))&v5_pre_topc(k2_tmap_1(X1,X4,X5,X2),X2,X4))&m1_subset_1(k2_tmap_1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4)))))&v1_funct_1(k2_tmap_1(X1,X4,X5,X3)))&v1_funct_2(k2_tmap_1(X1,X4,X5,X3),u1_struct_0(X3),u1_struct_0(X4)))&v5_pre_topc(k2_tmap_1(X1,X4,X5,X3),X3,X4))&m1_subset_1(k2_tmap_1(X1,X4,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))))=>(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4)))&v5_pre_topc(X5,X1,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))))))))))))), inference(assume_negation,[status(cth)],[t137_tmap_1])).
% 0.13/0.40  fof(c_0_6, plain, ![X15, X16, X17, X18, X19]:(((r1_tsep_1(X16,X17)|~r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&((((v1_funct_1(X19)|(~v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19))|~v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),u1_struct_0(X16),u1_struct_0(X18))|~v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),X16,X18)|~m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X18))))|~v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19))|~v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),u1_struct_0(X17),u1_struct_0(X18))|~v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),X17,X18)|~m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18)))))|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18)))))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18))|~r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(v1_funct_2(X19,u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))|(~v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19))|~v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),u1_struct_0(X16),u1_struct_0(X18))|~v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),X16,X18)|~m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X18))))|~v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19))|~v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),u1_struct_0(X17),u1_struct_0(X18))|~v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),X17,X18)|~m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18)))))|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18)))))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18))|~r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(v5_pre_topc(X19,k1_tsep_1(X15,X16,X17),X18)|(~v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19))|~v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),u1_struct_0(X16),u1_struct_0(X18))|~v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),X16,X18)|~m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X18))))|~v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19))|~v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),u1_struct_0(X17),u1_struct_0(X18))|~v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),X17,X18)|~m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18)))))|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18)))))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18))|~r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))))|(~v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19))|~v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),u1_struct_0(X16),u1_struct_0(X18))|~v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),X16,X18)|~m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X16,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X18))))|~v1_funct_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19))|~v1_funct_2(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),u1_struct_0(X17),u1_struct_0(X18))|~v5_pre_topc(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),X17,X18)|~m1_subset_1(k3_tmap_1(X15,X18,k1_tsep_1(X15,X16,X17),X17,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18)))))|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(X18)))))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18))|~r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))))&((((~v2_struct_0(esk1_3(X15,X16,X17))|~r1_tsep_1(X16,X17)|r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(v2_pre_topc(esk1_3(X15,X16,X17))|~r1_tsep_1(X16,X17)|r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(l1_pre_topc(esk1_3(X15,X16,X17))|~r1_tsep_1(X16,X17)|r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&((((v1_funct_1(esk2_3(X15,X16,X17))|~r1_tsep_1(X16,X17)|r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(v1_funct_2(esk2_3(X15,X16,X17),u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(esk1_3(X15,X16,X17)))|~r1_tsep_1(X16,X17)|r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(m1_subset_1(esk2_3(X15,X16,X17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(esk1_3(X15,X16,X17)))))|~r1_tsep_1(X16,X17)|r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(((((((((v1_funct_1(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X16,esk2_3(X15,X16,X17)))|~r1_tsep_1(X16,X17)|r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(v1_funct_2(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X16,esk2_3(X15,X16,X17)),u1_struct_0(X16),u1_struct_0(esk1_3(X15,X16,X17)))|~r1_tsep_1(X16,X17)|r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(v5_pre_topc(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X16,esk2_3(X15,X16,X17)),X16,esk1_3(X15,X16,X17))|~r1_tsep_1(X16,X17)|r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(m1_subset_1(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X16,esk2_3(X15,X16,X17)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(esk1_3(X15,X16,X17)))))|~r1_tsep_1(X16,X17)|r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(v1_funct_1(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X17,esk2_3(X15,X16,X17)))|~r1_tsep_1(X16,X17)|r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(v1_funct_2(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X17,esk2_3(X15,X16,X17)),u1_struct_0(X17),u1_struct_0(esk1_3(X15,X16,X17)))|~r1_tsep_1(X16,X17)|r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(v5_pre_topc(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X17,esk2_3(X15,X16,X17)),X17,esk1_3(X15,X16,X17))|~r1_tsep_1(X16,X17)|r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(m1_subset_1(k3_tmap_1(X15,esk1_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),X17,esk2_3(X15,X16,X17)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(esk1_3(X15,X16,X17)))))|~r1_tsep_1(X16,X17)|r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(~v1_funct_1(esk2_3(X15,X16,X17))|~v1_funct_2(esk2_3(X15,X16,X17),u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(esk1_3(X15,X16,X17)))|~v5_pre_topc(esk2_3(X15,X16,X17),k1_tsep_1(X15,X16,X17),esk1_3(X15,X16,X17))|~m1_subset_1(esk2_3(X15,X16,X17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X15,X16,X17)),u1_struct_0(esk1_3(X15,X16,X17)))))|~r1_tsep_1(X16,X17)|r3_tsep_1(X15,X16,X17)|(v2_struct_0(X17)|~m1_pre_topc(X17,X15))|(v2_struct_0(X16)|~m1_pre_topc(X16,X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t135_tmap_1])])])])])])).
% 0.13/0.40  fof(c_0_7, negated_conjecture, ![X28, X29]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk3_0))&(esk3_0=k1_tsep_1(esk3_0,esk4_0,esk5_0)&(((((~v2_struct_0(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0))&(v2_pre_topc(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(l1_pre_topc(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&((((v1_funct_1(esk7_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0))&(v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk6_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(((((((((v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0))&(v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk6_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),esk5_0,esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(~v1_funct_1(esk7_0)|~v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk6_0))|~v5_pre_topc(esk7_0,esk3_0,esk6_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))))&((r1_tsep_1(esk4_0,esk5_0)|r3_tsep_1(esk3_0,esk4_0,esk5_0))&((((v1_funct_1(X29)|(~v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk4_0))|~v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X28))|~v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk4_0),esk4_0,X28)|~m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X28))))|~v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk5_0))|~v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X28))|~v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk5_0),esk5_0,X28)|~m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X28)))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(esk3_0),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X28)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|r3_tsep_1(esk3_0,esk4_0,esk5_0))&(v1_funct_2(X29,u1_struct_0(esk3_0),u1_struct_0(X28))|(~v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk4_0))|~v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X28))|~v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk4_0),esk4_0,X28)|~m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X28))))|~v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk5_0))|~v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X28))|~v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk5_0),esk5_0,X28)|~m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X28)))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(esk3_0),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X28)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(v5_pre_topc(X29,esk3_0,X28)|(~v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk4_0))|~v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X28))|~v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk4_0),esk4_0,X28)|~m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X28))))|~v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk5_0))|~v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X28))|~v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk5_0),esk5_0,X28)|~m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X28)))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(esk3_0),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X28)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X28))))|(~v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk4_0))|~v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X28))|~v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk4_0),esk4_0,X28)|~m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X28))))|~v1_funct_1(k2_tmap_1(esk3_0,X28,X29,esk5_0))|~v1_funct_2(k2_tmap_1(esk3_0,X28,X29,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X28))|~v5_pre_topc(k2_tmap_1(esk3_0,X28,X29,esk5_0),esk5_0,X28)|~m1_subset_1(k2_tmap_1(esk3_0,X28,X29,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X28)))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(esk3_0),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X28)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|r3_tsep_1(esk3_0,esk4_0,esk5_0))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])])).
% 0.13/0.40  cnf(c_0_8, plain, (r1_tsep_1(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|~r3_tsep_1(X3,X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_9, negated_conjecture, (r1_tsep_1(esk4_0,esk5_0)|r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_10, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_11, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_12, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_13, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_14, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_17, plain, (v1_funct_2(esk2_3(X1,X2,X3),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_18, negated_conjecture, (r1_tsep_1(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14]), c_0_15]), c_0_16])).
% 0.13/0.40  cnf(c_0_19, plain, (v2_pre_topc(esk1_3(X1,X2,X3))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_20, plain, (l1_pre_topc(esk1_3(X1,X2,X3))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_21, plain, (v1_funct_1(esk2_3(X1,X2,X3))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_22, plain, (r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk1_3(X1,X2,X3))|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  fof(c_0_23, plain, ![X6, X7, X8, X9]:(v2_struct_0(X6)|~v2_pre_topc(X6)|~l1_pre_topc(X6)|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)|(~v1_funct_1(X8)|~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))|(~m1_pre_topc(X9,X6)|k2_tmap_1(X6,X7,X8,X9)=k2_partfun1(u1_struct_0(X6),u1_struct_0(X7),X8,u1_struct_0(X9)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.13/0.40  cnf(c_0_24, negated_conjecture, (r3_tsep_1(X1,esk4_0,esk5_0)|v1_funct_2(esk2_3(X1,esk4_0,esk5_0),u1_struct_0(k1_tsep_1(X1,esk4_0,esk5_0)),u1_struct_0(esk1_3(X1,esk4_0,esk5_0)))|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_15]), c_0_16])).
% 0.13/0.40  cnf(c_0_25, negated_conjecture, (esk3_0=k1_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_26, negated_conjecture, (r3_tsep_1(X1,esk4_0,esk5_0)|v2_pre_topc(esk1_3(X1,esk4_0,esk5_0))|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_18]), c_0_15]), c_0_16])).
% 0.13/0.40  cnf(c_0_27, negated_conjecture, (r3_tsep_1(X1,esk4_0,esk5_0)|l1_pre_topc(esk1_3(X1,esk4_0,esk5_0))|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_18]), c_0_15]), c_0_16])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (r3_tsep_1(X1,esk4_0,esk5_0)|v1_funct_1(esk2_3(X1,esk4_0,esk5_0))|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_18]), c_0_15]), c_0_16])).
% 0.13/0.40  cnf(c_0_29, negated_conjecture, (r3_tsep_1(X1,esk4_0,esk5_0)|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v2_struct_0(esk1_3(X1,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_18]), c_0_15]), c_0_16])).
% 0.13/0.40  cnf(c_0_30, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_31, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_32, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v1_funct_2(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_10]), c_0_25]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_34, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_35, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v1_funct_1(esk2_3(esk3_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (r3_tsep_1(X1,esk4_0,esk5_0)|m1_subset_1(esk2_3(X1,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk4_0,esk5_0)),u1_struct_0(esk1_3(X1,esk4_0,esk5_0)))))|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_18]), c_0_15]), c_0_16])).
% 0.13/0.40  fof(c_0_38, plain, ![X10, X11, X12, X13, X14]:(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|(~m1_pre_topc(X12,X10)|(~m1_pre_topc(X13,X10)|(~v1_funct_1(X14)|~v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X11))|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X11))))|(~m1_pre_topc(X13,X12)|k3_tmap_1(X10,X11,X12,X13,X14)=k2_partfun1(u1_struct_0(X12),u1_struct_0(X11),X14,u1_struct_0(X13)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.13/0.40  fof(c_0_39, plain, ![X22]:(~l1_pre_topc(X22)|m1_pre_topc(X22,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.13/0.40  cnf(c_0_40, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)),esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(X1))=k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1)|r3_tsep_1(esk3_0,esk4_0,esk5_0)|~m1_pre_topc(X1,esk3_0)|~m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_12]), c_0_13])]), c_0_14]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_10]), c_0_25]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_42, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_43, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.40  cnf(c_0_44, plain, (v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),X2,esk1_3(X1,X2,X3))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_45, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)),esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(X1))=k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),X1)|r3_tsep_1(esk3_0,esk4_0,esk5_0)|~m1_pre_topc(X1,esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.40  cnf(c_0_46, negated_conjecture, (k3_tmap_1(X1,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,X2,esk2_3(esk3_0,esk4_0,esk5_0))=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)),esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(X2))|r3_tsep_1(esk3_0,esk4_0,esk5_0)|v2_struct_0(X1)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_41]), c_0_36])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_43, c_0_12])).
% 0.13/0.40  cnf(c_0_48, plain, (v1_funct_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_49, plain, (v1_funct_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_50, plain, (v1_funct_2(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),u1_struct_0(X3),u1_struct_0(esk1_3(X1,X2,X3)))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_51, plain, (v1_funct_2(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_52, plain, (m1_subset_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(esk1_3(X1,X2,X3)))))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_53, plain, (m1_subset_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_54, plain, (v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),X3,esk1_3(X1,X2,X3))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk4_0,esk2_3(X1,esk4_0,esk5_0)),esk4_0,esk1_3(X1,esk4_0,esk5_0))|r3_tsep_1(X1,esk4_0,esk5_0)|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_18]), c_0_15]), c_0_16])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)),esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0))=k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0)|r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_11])).
% 0.13/0.40  cnf(c_0_57, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)),esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk4_0))=k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0))|r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_11]), c_0_11]), c_0_47]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_58, negated_conjecture, (r3_tsep_1(X1,esk4_0,esk5_0)|v1_funct_1(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk5_0,esk2_3(X1,esk4_0,esk5_0)))|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_18]), c_0_15]), c_0_16])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)),esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk5_0))=k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0)|r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_10])).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)),esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk5_0))=k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0))|r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_10]), c_0_10]), c_0_47]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (r3_tsep_1(X1,esk4_0,esk5_0)|v1_funct_1(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk4_0,esk2_3(X1,esk4_0,esk5_0)))|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_18]), c_0_15]), c_0_16])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (r3_tsep_1(X1,esk4_0,esk5_0)|v1_funct_2(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk5_0,esk2_3(X1,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(X1,esk4_0,esk5_0)))|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_18]), c_0_15]), c_0_16])).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, (r3_tsep_1(X1,esk4_0,esk5_0)|v1_funct_2(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk4_0,esk2_3(X1,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(X1,esk4_0,esk5_0)))|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_18]), c_0_15]), c_0_16])).
% 0.13/0.40  cnf(c_0_64, negated_conjecture, (r3_tsep_1(X1,esk4_0,esk5_0)|m1_subset_1(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk5_0,esk2_3(X1,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk1_3(X1,esk4_0,esk5_0)))))|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_18]), c_0_15]), c_0_16])).
% 0.13/0.40  cnf(c_0_65, negated_conjecture, (r3_tsep_1(X1,esk4_0,esk5_0)|m1_subset_1(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk4_0,esk2_3(X1,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(X1,esk4_0,esk5_0)))))|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_18]), c_0_15]), c_0_16])).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,esk4_0,esk5_0),k1_tsep_1(X1,esk4_0,esk5_0),esk5_0,esk2_3(X1,esk4_0,esk5_0)),esk5_0,esk1_3(X1,esk4_0,esk5_0))|r3_tsep_1(X1,esk4_0,esk5_0)|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_18]), c_0_15]), c_0_16])).
% 0.13/0.40  cnf(c_0_67, plain, (r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(esk2_3(X1,X2,X3))|~v1_funct_2(esk2_3(X1,X2,X3),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))|~v5_pre_topc(esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),esk1_3(X1,X2,X3))|~m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))))|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))|r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_10]), c_0_25]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_69, negated_conjecture, (k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0))=k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0)|r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.40  cnf(c_0_70, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_10]), c_0_25]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_71, negated_conjecture, (k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0))=k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0)|r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.40  cnf(c_0_72, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_10]), c_0_25]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_73, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_10]), c_0_25]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_74, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_10]), c_0_25]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_75, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|m1_subset_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_10]), c_0_25]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_76, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|m1_subset_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_10]), c_0_25]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_77, negated_conjecture, (v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))|r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_10]), c_0_25]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.40  cnf(c_0_78, plain, (r3_tsep_1(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v5_pre_topc(esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),esk1_3(X1,X2,X3))|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_67, c_0_21]), c_0_17]), c_0_30])).
% 0.13/0.40  cnf(c_0_79, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk6_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_80, negated_conjecture, (v5_pre_topc(X1,esk3_0,X2)|v2_struct_0(X2)|r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v1_funct_1(k2_tmap_1(esk3_0,X2,X1,esk4_0))|~v1_funct_2(k2_tmap_1(esk3_0,X2,X1,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(esk3_0,X2,X1,esk4_0),esk4_0,X2)|~m1_subset_1(k2_tmap_1(esk3_0,X2,X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))|~v1_funct_1(k2_tmap_1(esk3_0,X2,X1,esk5_0))|~v1_funct_2(k2_tmap_1(esk3_0,X2,X1,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(esk3_0,X2,X1,esk5_0),esk5_0,X2)|~m1_subset_1(k2_tmap_1(esk3_0,X2,X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_81, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))|r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.13/0.40  cnf(c_0_82, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.13/0.40  cnf(c_0_83, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v1_funct_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0))), inference(spm,[status(thm)],[c_0_72, c_0_69])).
% 0.13/0.40  cnf(c_0_84, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_73, c_0_71])).
% 0.13/0.40  cnf(c_0_85, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|v1_funct_2(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_74, c_0_69])).
% 0.13/0.40  cnf(c_0_86, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))), inference(spm,[status(thm)],[c_0_75, c_0_71])).
% 0.13/0.40  cnf(c_0_87, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|m1_subset_1(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))), inference(spm,[status(thm)],[c_0_76, c_0_69])).
% 0.13/0.40  cnf(c_0_88, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),esk2_3(esk3_0,esk4_0,esk5_0),esk5_0),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))|r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_77, c_0_71])).
% 0.13/0.40  cnf(c_0_89, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0,esk1_3(esk3_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_25]), c_0_18]), c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_15]), c_0_16]), c_0_14])).
% 0.13/0.40  cnf(c_0_90, negated_conjecture, (v1_funct_1(esk7_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_91, negated_conjecture, (l1_pre_topc(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_92, negated_conjecture, (v2_pre_topc(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_93, negated_conjecture, (~v2_struct_0(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_94, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_95, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk6_0))|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_18])])).
% 0.13/0.40  cnf(c_0_96, negated_conjecture, (r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_33]), c_0_34]), c_0_35]), c_0_82]), c_0_83]), c_0_32]), c_0_84]), c_0_85]), c_0_41]), c_0_86]), c_0_87]), c_0_88]), c_0_36]), c_0_89])).
% 0.13/0.40  cnf(c_0_97, negated_conjecture, (v1_funct_1(esk7_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_18])])).
% 0.13/0.40  cnf(c_0_98, negated_conjecture, (l1_pre_topc(esk6_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_18])])).
% 0.13/0.40  cnf(c_0_99, negated_conjecture, (v2_pre_topc(esk6_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_18])])).
% 0.13/0.40  cnf(c_0_100, negated_conjecture, (~r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v2_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_18])])).
% 0.13/0.40  cnf(c_0_101, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0))))|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_18])])).
% 0.13/0.40  cnf(c_0_102, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96])])).
% 0.13/0.40  cnf(c_0_103, negated_conjecture, (v1_funct_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_96])])).
% 0.13/0.40  cnf(c_0_104, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_96])])).
% 0.13/0.40  cnf(c_0_105, negated_conjecture, (v2_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_96])])).
% 0.13/0.40  cnf(c_0_106, negated_conjecture, (~v2_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_96])])).
% 0.13/0.40  cnf(c_0_107, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_96])])).
% 0.13/0.40  cnf(c_0_108, negated_conjecture, (~v1_funct_1(esk7_0)|~v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk6_0))|~v5_pre_topc(esk7_0,esk3_0,esk6_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_109, plain, (v5_pre_topc(X1,k1_tsep_1(X2,X3,X4),X5)|v2_struct_0(X5)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1))|~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),u1_struct_0(X3),u1_struct_0(X5))|~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),X3,X5)|~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X5))))|~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1))|~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),u1_struct_0(X4),u1_struct_0(X5))|~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),X4,X5)|~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(k1_tsep_1(X2,X3,X4)),u1_struct_0(X5))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X4)),u1_struct_0(X5))))|~v2_pre_topc(X5)|~l1_pre_topc(X5)|~r3_tsep_1(X2,X3,X4)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_110, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk6_0),esk7_0,u1_struct_0(X1))=k2_tmap_1(esk3_0,esk6_0,esk7_0,X1)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_102]), c_0_103]), c_0_104]), c_0_12]), c_0_105]), c_0_13])]), c_0_106]), c_0_14]), c_0_107])])).
% 0.13/0.40  cnf(c_0_111, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),esk5_0,esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_112, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_113, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk6_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_114, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_115, negated_conjecture, (~v5_pre_topc(esk7_0,esk3_0,esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk6_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_108, c_0_90]), c_0_79])).
% 0.13/0.40  cnf(c_0_116, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_117, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_118, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_119, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_120, negated_conjecture, (v5_pre_topc(X1,esk3_0,X2)|v2_struct_0(X2)|~v5_pre_topc(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1),esk5_0,X2)|~v5_pre_topc(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1),esk4_0,X2)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)|~m1_subset_1(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))|~m1_subset_1(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X2))))|~v1_funct_2(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1),u1_struct_0(esk5_0),u1_struct_0(X2))|~v1_funct_2(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(X2))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(X2))|~v1_funct_1(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1))|~v1_funct_1(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_25]), c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_15]), c_0_16]), c_0_14])).
% 0.13/0.41  cnf(c_0_121, negated_conjecture, (k3_tmap_1(X1,esk6_0,esk3_0,X2,esk7_0)=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk6_0),esk7_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_102]), c_0_103]), c_0_104]), c_0_105])]), c_0_106]), c_0_107])])).
% 0.13/0.41  cnf(c_0_122, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk5_0))=k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_110, c_0_10])).
% 0.13/0.41  cnf(c_0_123, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),esk5_0,esk6_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_18])])).
% 0.13/0.41  cnf(c_0_124, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_18])])).
% 0.13/0.41  cnf(c_0_125, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk6_0))|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_18])])).
% 0.13/0.41  cnf(c_0_126, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0))|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_18])])).
% 0.13/0.41  cnf(c_0_127, negated_conjecture, (~v5_pre_topc(esk7_0,esk3_0,esk6_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_18])]), c_0_101])).
% 0.13/0.41  cnf(c_0_128, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk6_0),esk7_0,u1_struct_0(esk4_0))=k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0)), inference(spm,[status(thm)],[c_0_110, c_0_11])).
% 0.13/0.41  cnf(c_0_129, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk6_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_18])])).
% 0.13/0.41  cnf(c_0_130, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_18])])).
% 0.13/0.41  cnf(c_0_131, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0))|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_18])])).
% 0.13/0.41  cnf(c_0_132, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0))|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_18])])).
% 0.13/0.41  cnf(c_0_133, negated_conjecture, (v5_pre_topc(X1,esk3_0,X2)|v2_struct_0(X2)|~v5_pre_topc(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1),esk5_0,X2)|~v5_pre_topc(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1),esk4_0,X2)|~m1_subset_1(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))|~m1_subset_1(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X2))))|~v1_funct_2(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1),u1_struct_0(esk5_0),u1_struct_0(X2))|~v1_funct_2(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(X2))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(X2))|~v1_funct_1(k3_tmap_1(esk3_0,X2,esk3_0,esk5_0,X1))|~v1_funct_1(k3_tmap_1(esk3_0,X2,esk3_0,esk4_0,X1))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_96])])).
% 0.13/0.41  cnf(c_0_134, negated_conjecture, (k3_tmap_1(esk3_0,esk6_0,esk3_0,esk5_0,esk7_0)=k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_10]), c_0_122]), c_0_10]), c_0_47]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.41  cnf(c_0_135, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_96])])).
% 0.13/0.41  cnf(c_0_136, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_96])])).
% 0.13/0.41  cnf(c_0_137, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_96])])).
% 0.13/0.41  cnf(c_0_138, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_96])])).
% 0.13/0.41  cnf(c_0_139, negated_conjecture, (~v5_pre_topc(esk7_0,esk3_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_96])])).
% 0.13/0.41  cnf(c_0_140, negated_conjecture, (k3_tmap_1(esk3_0,esk6_0,esk3_0,esk4_0,esk7_0)=k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_11]), c_0_128]), c_0_11]), c_0_47]), c_0_12]), c_0_13])]), c_0_14])).
% 0.13/0.41  cnf(c_0_141, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_96])])).
% 0.13/0.41  cnf(c_0_142, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_96])])).
% 0.13/0.41  cnf(c_0_143, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131, c_0_96])])).
% 0.13/0.41  cnf(c_0_144, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk6_0,esk7_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132, c_0_96])])).
% 0.13/0.41  cnf(c_0_145, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_134]), c_0_135]), c_0_136]), c_0_107]), c_0_137]), c_0_102]), c_0_138]), c_0_103]), c_0_104]), c_0_105])]), c_0_139]), c_0_106]), c_0_140]), c_0_141]), c_0_140]), c_0_142]), c_0_140]), c_0_143]), c_0_140]), c_0_144])]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 146
% 0.13/0.41  # Proof object clause steps            : 135
% 0.13/0.41  # Proof object formula steps           : 11
% 0.13/0.41  # Proof object conjectures             : 117
% 0.13/0.41  # Proof object clause conjectures      : 114
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 45
% 0.13/0.41  # Proof object initial formulas used   : 5
% 0.13/0.41  # Proof object generating inferences   : 57
% 0.13/0.41  # Proof object simplifying inferences  : 292
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 5
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 51
% 0.13/0.41  # Removed in clause preprocessing      : 6
% 0.13/0.41  # Initial clauses in saturation        : 45
% 0.13/0.41  # Processed clauses                    : 202
% 0.13/0.41  # ...of these trivial                  : 0
% 0.13/0.41  # ...subsumed                          : 0
% 0.13/0.41  # ...remaining for further processing  : 201
% 0.13/0.41  # Other redundant clauses eliminated   : 0
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 2
% 0.13/0.41  # Backward-rewritten                   : 76
% 0.13/0.41  # Generated clauses                    : 94
% 0.13/0.41  # ...of the previous two non-trivial   : 115
% 0.13/0.41  # Contextual simplify-reflections      : 67
% 0.13/0.41  # Paramodulations                      : 94
% 0.13/0.41  # Factorizations                       : 0
% 0.13/0.41  # Equation resolutions                 : 0
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 78
% 0.13/0.41  #    Positive orientable unit clauses  : 28
% 0.13/0.41  #    Positive unorientable unit clauses: 0
% 0.13/0.41  #    Negative unit clauses             : 5
% 0.13/0.41  #    Non-unit-clauses                  : 45
% 0.13/0.41  # Current number of unprocessed clauses: 1
% 0.13/0.41  # ...number of literals in the above   : 8
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 123
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 7397
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 1195
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 69
% 0.13/0.41  # Unit Clause-clause subsumption calls : 113
% 0.13/0.41  # Rewrite failures with RHS unbound    : 0
% 0.13/0.41  # BW rewrite match attempts            : 13
% 0.13/0.41  # BW rewrite match successes           : 2
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 15151
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.058 s
% 0.13/0.41  # System time              : 0.003 s
% 0.13/0.41  # Total time               : 0.061 s
% 0.13/0.41  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
