%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:29 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  171 (3433 expanded)
%              Number of clauses        :  112 ( 597 expanded)
%              Number of leaves         :   12 (1628 expanded)
%              Depth                    :   25
%              Number of atoms          : 1768 (88369 expanded)
%              Number of equality atoms :  533 (5128 expanded)
%              Maximal formula depth    :   29 (  10 average)
%              Maximal clause size      :   54 (   8 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                              & k1_tsep_1(X0,X2,X3) = X0 )
                           => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                              & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                              & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                                & k1_tsep_1(X0,X2,X3) = X0 )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(X0,X2,X3) = X0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(X0,X2,X3) = X0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
          & k1_tsep_1(X0,X2,X3) = X0
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(X5,X3,X1)
          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK5),X0,X1)
          | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK5),u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK5)) )
        & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,sK5)),sK5)
        & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,sK5)),X4)
        & k1_tsep_1(X0,X2,X3) = X0
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(sK5,X3,X1)
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
              & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
              & k1_tsep_1(X0,X2,X3) = X0
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v5_pre_topc(X5,X3,X1)
              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(X4,X2,X1)
          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,sK4,X5),X0,X1)
              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,sK4,X5),u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,sK4,X5)) )
            & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,sK4,X5)),X5)
            & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,sK4,X5)),sK4)
            & k1_tsep_1(X0,X2,X3) = X0
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v5_pre_topc(X5,X3,X1)
            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(sK4,X2,X1)
        & v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                    | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                    | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                  & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                  & k1_tsep_1(X0,X2,X3) = X0
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(X5,X3,X1)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(X4,X2,X1)
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & v1_borsuk_1(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,sK3,X4,X5),X0,X1)
                  | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,sK3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,sK3,X4,X5)) )
                & r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK3),sK3,k10_tmap_1(X0,X1,X2,sK3,X4,X5)),X5)
                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK3),X2,k10_tmap_1(X0,X1,X2,sK3,X4,X5)),X4)
                & k1_tsep_1(X0,X2,sK3) = X0
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                & v5_pre_topc(X5,sK3,X1)
                & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(X4,X2,X1)
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & v1_borsuk_1(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                        | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                      & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                      & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                      & k1_tsep_1(X0,X2,X3) = X0
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(X5,X3,X1)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(X4,X2,X1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & v1_borsuk_1(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & v1_borsuk_1(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k10_tmap_1(X0,X1,sK2,X3,X4,X5),X0,X1)
                      | ~ v1_funct_2(k10_tmap_1(X0,X1,sK2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(k10_tmap_1(X0,X1,sK2,X3,X4,X5)) )
                    & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK2,X3),X3,k10_tmap_1(X0,X1,sK2,X3,X4,X5)),X5)
                    & r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK2,X3),sK2,k10_tmap_1(X0,X1,sK2,X3,X4,X5)),X4)
                    & k1_tsep_1(X0,sK2,X3) = X0
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(X5,X3,X1)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                & v5_pre_topc(X4,sK2,X1)
                & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & v1_borsuk_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & v1_borsuk_1(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(X0,X2,X3) = X0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(X0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                          | ~ v5_pre_topc(k10_tmap_1(X0,sK1,X2,X3,X4,X5),X0,sK1)
                          | ~ v1_funct_2(k10_tmap_1(X0,sK1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(sK1))
                          | ~ v1_funct_1(k10_tmap_1(X0,sK1,X2,X3,X4,X5)) )
                        & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(X0,sK1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,sK1,X2,X3,X4,X5)),X5)
                        & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,sK1,X2,X3,X4,X5)),X4)
                        & k1_tsep_1(X0,X2,X3) = X0
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                        & v5_pre_topc(X5,X3,sK1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                    & v5_pre_topc(X4,X2,sK1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & v1_borsuk_1(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & v1_borsuk_1(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                            & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                            & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                            & k1_tsep_1(X0,X2,X3) = X0
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),sK0,X1)
                            | ~ v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(sK0,X2,X3) = sK0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & v1_borsuk_1(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & v1_borsuk_1(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) )
    & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)
    & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    & k1_tsep_1(sK0,sK2,sK3) = sK0
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v5_pre_topc(sK5,sK3,sK1)
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v5_pre_topc(sK4,sK2,sK1)
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & v1_borsuk_1(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & v1_borsuk_1(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f19,f27,f26,f25,f24,f23,f22])).

fof(f66,plain,(
    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                            <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                          <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                          <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                              | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                            & ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                              | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                            & ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    v5_pre_topc(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( r4_tsep_1(X0,X2,X3)
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    v1_borsuk_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    v1_borsuk_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_borsuk_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f28])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r4_tsep_1(X0,X2,X3)
                                & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_16,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1251,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1972,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1251])).

cnf(c_18,negated_conjecture,
    ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1249,negated_conjecture,
    ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2039,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1972,c_1249])).

cnf(c_5,plain,
    ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X5)
    | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X3,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X4)
    | r2_funct_2(u1_struct_0(k2_tsep_1(X2,X3,X0)),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X3,X0),X4),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X3,X0),X5))
    | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | r1_tsep_1(X3,X0)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1259,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_55),u1_struct_0(X1_55),k3_tmap_1(X2_55,X1_55,k1_tsep_1(X2_55,X3_55,X0_55),X0_55,k10_tmap_1(X2_55,X1_55,X3_55,X0_55,X0_53,X1_53)),X1_53)
    | ~ r2_funct_2(u1_struct_0(X3_55),u1_struct_0(X1_55),k3_tmap_1(X2_55,X1_55,k1_tsep_1(X2_55,X3_55,X0_55),X3_55,k10_tmap_1(X2_55,X1_55,X3_55,X0_55,X0_53,X1_53)),X0_53)
    | r2_funct_2(u1_struct_0(k2_tsep_1(X2_55,X3_55,X0_55)),u1_struct_0(X1_55),k3_tmap_1(X2_55,X1_55,X3_55,k2_tsep_1(X2_55,X3_55,X0_55),X0_53),k3_tmap_1(X2_55,X1_55,X0_55,k2_tsep_1(X2_55,X3_55,X0_55),X1_53))
    | ~ v1_funct_2(X1_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X0_53,u1_struct_0(X3_55),u1_struct_0(X1_55))
    | r1_tsep_1(X3_55,X0_55)
    | ~ m1_pre_topc(X0_55,X2_55)
    | ~ m1_pre_topc(X3_55,X2_55)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X2_55)
    | ~ v2_pre_topc(X1_55)
    | ~ l1_pre_topc(X2_55)
    | ~ l1_pre_topc(X1_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X3_55)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1964,plain,
    ( r2_funct_2(u1_struct_0(X0_55),u1_struct_0(X1_55),k3_tmap_1(X2_55,X1_55,k1_tsep_1(X2_55,X3_55,X0_55),X0_55,k10_tmap_1(X2_55,X1_55,X3_55,X0_55,X0_53,X1_53)),X1_53) != iProver_top
    | r2_funct_2(u1_struct_0(X3_55),u1_struct_0(X1_55),k3_tmap_1(X2_55,X1_55,k1_tsep_1(X2_55,X3_55,X0_55),X3_55,k10_tmap_1(X2_55,X1_55,X3_55,X0_55,X0_53,X1_53)),X0_53) != iProver_top
    | r2_funct_2(u1_struct_0(k2_tsep_1(X2_55,X3_55,X0_55)),u1_struct_0(X1_55),k3_tmap_1(X2_55,X1_55,X3_55,k2_tsep_1(X2_55,X3_55,X0_55),X0_53),k3_tmap_1(X2_55,X1_55,X0_55,k2_tsep_1(X2_55,X3_55,X0_55),X1_53)) = iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X3_55),u1_struct_0(X1_55)) != iProver_top
    | r1_tsep_1(X3_55,X0_55) = iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_pre_topc(X3_55,X2_55) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1259])).

cnf(c_4046,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK2,k2_tsep_1(sK0,sK2,sK3),X0_53),k3_tmap_1(sK0,X0_55,sK3,k2_tsep_1(sK0,sK2,sK3),X1_53)) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK0,sK3,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X1_53) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X0_53) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
    | r1_tsep_1(sK2,sK3) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_1964])).

cnf(c_4047,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK2,k2_tsep_1(sK0,sK2,sK3),X0_53),k3_tmap_1(sK0,X0_55,sK3,k2_tsep_1(sK0,sK2,sK3),X1_53)) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK0,sK3,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X1_53) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK0,sK2,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X0_53) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
    | r1_tsep_1(sK2,sK3) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4046,c_1249])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_39,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_40,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_41,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_42,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_43,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_44,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_45,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_47,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_48,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_50,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_51,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_52,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_53,plain,
    ( v5_pre_topc(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_54,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_55,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_56,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v5_pre_topc(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_57,plain,
    ( v5_pre_topc(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_58,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X3,X4,X2)
    | v5_pre_topc(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_tsep_1(X5,X4,X1),X2)
    | ~ r4_tsep_1(X5,X4,X1)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ r1_tsep_1(X4,X1)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1254,plain,
    ( ~ v5_pre_topc(X0_53,X0_55,X1_55)
    | ~ v5_pre_topc(X1_53,X2_55,X1_55)
    | v5_pre_topc(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),k1_tsep_1(X3_55,X2_55,X0_55),X1_55)
    | ~ r4_tsep_1(X3_55,X2_55,X0_55)
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
    | ~ r1_tsep_1(X2_55,X0_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X3_55)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1969,plain,
    ( v5_pre_topc(X0_53,X0_55,X1_55) != iProver_top
    | v5_pre_topc(X1_53,X2_55,X1_55) != iProver_top
    | v5_pre_topc(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),k1_tsep_1(X3_55,X2_55,X0_55),X1_55) = iProver_top
    | r4_tsep_1(X3_55,X2_55,X0_55) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
    | r1_tsep_1(X2_55,X0_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1254])).

cnf(c_3948,plain,
    ( v5_pre_topc(X0_53,sK3,X0_55) != iProver_top
    | v5_pre_topc(X1_53,sK2,X0_55) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),sK0,X0_55) = iProver_top
    | r4_tsep_1(sK0,sK2,sK3) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
    | r1_tsep_1(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_1969])).

cnf(c_31,negated_conjecture,
    ( v1_borsuk_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_46,plain,
    ( v1_borsuk_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,negated_conjecture,
    ( v1_borsuk_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_49,plain,
    ( v1_borsuk_1(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14,plain,
    ( r4_tsep_1(X0,X1,X2)
    | ~ v1_borsuk_1(X2,X0)
    | ~ v1_borsuk_1(X1,X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1253,plain,
    ( r4_tsep_1(X0_55,X1_55,X2_55)
    | ~ v1_borsuk_1(X2_55,X0_55)
    | ~ v1_borsuk_1(X1_55,X0_55)
    | ~ m1_pre_topc(X2_55,X0_55)
    | ~ m1_pre_topc(X1_55,X0_55)
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X0_55)
    | v2_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2522,plain,
    ( r4_tsep_1(sK0,X0_55,sK3)
    | ~ v1_borsuk_1(X0_55,sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(X0_55,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1253])).

cnf(c_2681,plain,
    ( r4_tsep_1(sK0,sK2,sK3)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2522])).

cnf(c_2682,plain,
    ( r4_tsep_1(sK0,sK2,sK3) = iProver_top
    | v1_borsuk_1(sK3,sK0) != iProver_top
    | v1_borsuk_1(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2681])).

cnf(c_3969,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | r1_tsep_1(sK2,sK3) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
    | v5_pre_topc(X0_53,sK3,X0_55) != iProver_top
    | v5_pre_topc(X1_53,sK2,X0_55) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),sK0,X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3948,c_39,c_40,c_41,c_45,c_46,c_47,c_48,c_49,c_50,c_2682])).

cnf(c_3970,plain,
    ( v5_pre_topc(X0_53,sK3,X0_55) != iProver_top
    | v5_pre_topc(X1_53,sK2,X0_55) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),sK0,X0_55) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
    | r1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_3969])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1263,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
    | v1_funct_2(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X3_55)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1960,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55)) = iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1263])).

cnf(c_3070,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),u1_struct_0(sK0),u1_struct_0(X0_55)) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_1960])).

cnf(c_3289,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),u1_struct_0(sK0),u1_struct_0(X0_55)) = iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3070,c_39,c_40,c_41,c_45,c_47,c_48,c_50])).

cnf(c_3290,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),u1_struct_0(sK0),u1_struct_0(X0_55)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_3289])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1264,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | m1_subset_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X3_55)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1959,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55)))) = iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1264])).

cnf(c_2590,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_55)))) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_1959])).

cnf(c_3354,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_55)))) = iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2590,c_39,c_40,c_41,c_45,c_47,c_48,c_50])).

cnf(c_3355,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_55)))) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_3354])).

cnf(c_15,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1252,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1971,plain,
    ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1252])).

cnf(c_61,plain,
    ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1262,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X3_55)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | v1_funct_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2542,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X0_55,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(X1_53)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k10_tmap_1(sK0,X1_55,X0_55,sK3,X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_1262])).

cnf(c_2761,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55))
    | ~ v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(X1_53)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53)) ),
    inference(instantiation,[status(thm)],[c_2542])).

cnf(c_2821,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2761])).

cnf(c_2822,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2821])).

cnf(c_2824,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2822])).

cnf(c_3281,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1971,c_39,c_40,c_41,c_42,c_43,c_44,c_45,c_47,c_48,c_50,c_51,c_52,c_54,c_55,c_56,c_58,c_61,c_2824])).

cnf(c_3282,plain,
    ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3281])).

cnf(c_3370,plain,
    ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3355,c_3282])).

cnf(c_3373,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3370,c_42,c_43,c_44,c_51,c_52,c_54,c_55,c_56,c_58])).

cnf(c_3374,plain,
    ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3373])).

cnf(c_3379,plain,
    ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3290,c_3374])).

cnf(c_3432,plain,
    ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3379,c_42,c_43,c_44,c_51,c_52,c_54,c_55,c_56,c_58])).

cnf(c_3988,plain,
    ( v5_pre_topc(sK5,sK3,sK1) != iProver_top
    | v5_pre_topc(sK4,sK2,sK1) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3970,c_3432])).

cnf(c_4052,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK2,k2_tsep_1(sK0,sK2,sK3),X0_53),k3_tmap_1(sK0,X0_55,sK3,k2_tsep_1(sK0,sK2,sK3),X1_53)) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK0,sK3,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X1_53) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK0,sK2,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X0_53) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4047,c_39,c_40,c_41,c_42,c_43,c_44,c_45,c_47,c_48,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_3988])).

cnf(c_4053,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK2,k2_tsep_1(sK0,sK2,sK3),X0_53),k3_tmap_1(sK0,X0_55,sK3,k2_tsep_1(sK0,sK2,sK3),X1_53)) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK0,sK3,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X1_53) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK0,sK2,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X0_53) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4052])).

cnf(c_4070,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2039,c_4053])).

cnf(c_17,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_59,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_60,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2656,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_55),u1_struct_0(X1_55),k3_tmap_1(sK0,X1_55,k1_tsep_1(sK0,X0_55,sK3),X0_55,k10_tmap_1(sK0,X1_55,X0_55,sK3,X0_53,X1_53)),X0_53)
    | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,X0_55,sK3)),u1_struct_0(X1_55),k3_tmap_1(sK0,X1_55,X0_55,k2_tsep_1(sK0,X0_55,sK3),X0_53),k3_tmap_1(sK0,X1_55,sK3,k2_tsep_1(sK0,X0_55,sK3),X1_53))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1_55),k3_tmap_1(sK0,X1_55,k1_tsep_1(sK0,X0_55,sK3),sK3,k10_tmap_1(sK0,X1_55,X0_55,sK3,X0_53,X1_53)),X1_53)
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(X1_55))
    | r1_tsep_1(X0_55,sK3)
    | ~ m1_pre_topc(X0_55,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(instantiation,[status(thm)],[c_1259])).

cnf(c_2985,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK2,k2_tsep_1(sK0,sK2,sK3),X0_53),k3_tmap_1(sK0,X0_55,sK3,k2_tsep_1(sK0,sK2,sK3),X1_53))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X1_53)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X0_53)
    | ~ v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(X0_55))
    | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_55))
    | r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55))))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(instantiation,[status(thm)],[c_2656])).

cnf(c_3426,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),X0_53),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5))
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,sK5)),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,sK5)),X0_53)
    | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2985])).

cnf(c_3427,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),X0_53),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,sK5)),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,sK5)),X0_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | r1_tsep_1(sK2,sK3) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3426])).

cnf(c_3429,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r1_tsep_1(sK2,sK3) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3427])).

cnf(c_4453,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4070,c_39,c_40,c_41,c_42,c_43,c_44,c_45,c_47,c_48,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_3429,c_3988])).

cnf(c_7,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X1,X2)),u1_struct_0(X3),k3_tmap_1(X0,X3,X1,k2_tsep_1(X0,X1,X2),X4),k3_tmap_1(X0,X3,X2,k2_tsep_1(X0,X1,X2),X5))
    | ~ v5_pre_topc(X5,X2,X3)
    | ~ v5_pre_topc(X4,X1,X3)
    | v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
    | ~ r4_tsep_1(X0,X1,X2)
    | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1257,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0_55,X1_55,X2_55)),u1_struct_0(X3_55),k3_tmap_1(X0_55,X3_55,X1_55,k2_tsep_1(X0_55,X1_55,X2_55),X0_53),k3_tmap_1(X0_55,X3_55,X2_55,k2_tsep_1(X0_55,X1_55,X2_55),X1_53))
    | ~ v5_pre_topc(X1_53,X2_55,X3_55)
    | ~ v5_pre_topc(X0_53,X1_55,X3_55)
    | v5_pre_topc(k10_tmap_1(X0_55,X3_55,X1_55,X2_55,X0_53,X1_53),k1_tsep_1(X0_55,X1_55,X2_55),X3_55)
    | ~ r4_tsep_1(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X3_55))
    | ~ v1_funct_2(X0_53,u1_struct_0(X1_55),u1_struct_0(X3_55))
    | r1_tsep_1(X1_55,X2_55)
    | ~ m1_pre_topc(X2_55,X0_55)
    | ~ m1_pre_topc(X1_55,X0_55)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X3_55))))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X3_55))))
    | ~ v2_pre_topc(X3_55)
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X3_55)
    | ~ l1_pre_topc(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X3_55)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1966,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(X0_55,X1_55,X2_55)),u1_struct_0(X3_55),k3_tmap_1(X0_55,X3_55,X1_55,k2_tsep_1(X0_55,X1_55,X2_55),X0_53),k3_tmap_1(X0_55,X3_55,X2_55,k2_tsep_1(X0_55,X1_55,X2_55),X1_53)) != iProver_top
    | v5_pre_topc(X1_53,X2_55,X3_55) != iProver_top
    | v5_pre_topc(X0_53,X1_55,X3_55) != iProver_top
    | v5_pre_topc(k10_tmap_1(X0_55,X3_55,X1_55,X2_55,X0_53,X1_53),k1_tsep_1(X0_55,X1_55,X2_55),X3_55) = iProver_top
    | r4_tsep_1(X0_55,X1_55,X2_55) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X3_55)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X1_55),u1_struct_0(X3_55)) != iProver_top
    | r1_tsep_1(X1_55,X2_55) = iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X3_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X3_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1257])).

cnf(c_2311,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(X0_55,X1_55,X2_55)),u1_struct_0(X3_55),k3_tmap_1(X0_55,X3_55,X1_55,k2_tsep_1(X0_55,X1_55,X2_55),X0_53),k3_tmap_1(X0_55,X3_55,X2_55,k2_tsep_1(X0_55,X1_55,X2_55),X1_53)) != iProver_top
    | v5_pre_topc(X1_53,X2_55,X3_55) != iProver_top
    | v5_pre_topc(X0_53,X1_55,X3_55) != iProver_top
    | v5_pre_topc(k10_tmap_1(X0_55,X3_55,X1_55,X2_55,X0_53,X1_53),k1_tsep_1(X0_55,X1_55,X2_55),X3_55) = iProver_top
    | r4_tsep_1(X0_55,X1_55,X2_55) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X3_55)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X1_55),u1_struct_0(X3_55)) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X3_55)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X3_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1966,c_1969])).

cnf(c_4621,plain,
    ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) = iProver_top
    | v5_pre_topc(sK5,sK3,sK1) != iProver_top
    | v5_pre_topc(sK4,sK2,sK1) != iProver_top
    | r4_tsep_1(sK0,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4453,c_2311])).

cnf(c_4622,plain,
    ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) = iProver_top
    | v5_pre_topc(sK5,sK3,sK1) != iProver_top
    | v5_pre_topc(sK4,sK2,sK1) != iProver_top
    | r4_tsep_1(sK0,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4621,c_1249])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4622,c_3379,c_2682,c_58,c_57,c_56,c_55,c_54,c_53,c_52,c_51,c_50,c_49,c_48,c_47,c_46,c_45,c_44,c_43,c_42,c_41,c_40,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:23:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.53/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.00  
% 2.53/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.53/1.00  
% 2.53/1.00  ------  iProver source info
% 2.53/1.00  
% 2.53/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.53/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.53/1.00  git: non_committed_changes: false
% 2.53/1.00  git: last_make_outside_of_git: false
% 2.53/1.00  
% 2.53/1.00  ------ 
% 2.53/1.00  
% 2.53/1.00  ------ Input Options
% 2.53/1.00  
% 2.53/1.00  --out_options                           all
% 2.53/1.00  --tptp_safe_out                         true
% 2.53/1.00  --problem_path                          ""
% 2.53/1.00  --include_path                          ""
% 2.53/1.00  --clausifier                            res/vclausify_rel
% 2.53/1.00  --clausifier_options                    --mode clausify
% 2.53/1.00  --stdin                                 false
% 2.53/1.00  --stats_out                             all
% 2.53/1.00  
% 2.53/1.00  ------ General Options
% 2.53/1.00  
% 2.53/1.00  --fof                                   false
% 2.53/1.00  --time_out_real                         305.
% 2.53/1.00  --time_out_virtual                      -1.
% 2.53/1.00  --symbol_type_check                     false
% 2.53/1.00  --clausify_out                          false
% 2.53/1.00  --sig_cnt_out                           false
% 2.53/1.00  --trig_cnt_out                          false
% 2.53/1.00  --trig_cnt_out_tolerance                1.
% 2.53/1.00  --trig_cnt_out_sk_spl                   false
% 2.53/1.00  --abstr_cl_out                          false
% 2.53/1.00  
% 2.53/1.00  ------ Global Options
% 2.53/1.00  
% 2.53/1.00  --schedule                              default
% 2.53/1.00  --add_important_lit                     false
% 2.53/1.00  --prop_solver_per_cl                    1000
% 2.53/1.00  --min_unsat_core                        false
% 2.53/1.00  --soft_assumptions                      false
% 2.53/1.00  --soft_lemma_size                       3
% 2.53/1.00  --prop_impl_unit_size                   0
% 2.53/1.00  --prop_impl_unit                        []
% 2.53/1.00  --share_sel_clauses                     true
% 2.53/1.00  --reset_solvers                         false
% 2.53/1.00  --bc_imp_inh                            [conj_cone]
% 2.53/1.00  --conj_cone_tolerance                   3.
% 2.53/1.00  --extra_neg_conj                        none
% 2.53/1.00  --large_theory_mode                     true
% 2.53/1.00  --prolific_symb_bound                   200
% 2.53/1.00  --lt_threshold                          2000
% 2.53/1.00  --clause_weak_htbl                      true
% 2.53/1.00  --gc_record_bc_elim                     false
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing Options
% 2.53/1.00  
% 2.53/1.00  --preprocessing_flag                    true
% 2.53/1.00  --time_out_prep_mult                    0.1
% 2.53/1.00  --splitting_mode                        input
% 2.53/1.00  --splitting_grd                         true
% 2.53/1.00  --splitting_cvd                         false
% 2.53/1.00  --splitting_cvd_svl                     false
% 2.53/1.00  --splitting_nvd                         32
% 2.53/1.00  --sub_typing                            true
% 2.53/1.00  --prep_gs_sim                           true
% 2.53/1.00  --prep_unflatten                        true
% 2.53/1.00  --prep_res_sim                          true
% 2.53/1.00  --prep_upred                            true
% 2.53/1.00  --prep_sem_filter                       exhaustive
% 2.53/1.00  --prep_sem_filter_out                   false
% 2.53/1.00  --pred_elim                             true
% 2.53/1.00  --res_sim_input                         true
% 2.53/1.00  --eq_ax_congr_red                       true
% 2.53/1.00  --pure_diseq_elim                       true
% 2.53/1.00  --brand_transform                       false
% 2.53/1.00  --non_eq_to_eq                          false
% 2.53/1.00  --prep_def_merge                        true
% 2.53/1.00  --prep_def_merge_prop_impl              false
% 2.53/1.00  --prep_def_merge_mbd                    true
% 2.53/1.00  --prep_def_merge_tr_red                 false
% 2.53/1.00  --prep_def_merge_tr_cl                  false
% 2.53/1.00  --smt_preprocessing                     true
% 2.53/1.00  --smt_ac_axioms                         fast
% 2.53/1.00  --preprocessed_out                      false
% 2.53/1.00  --preprocessed_stats                    false
% 2.53/1.00  
% 2.53/1.00  ------ Abstraction refinement Options
% 2.53/1.00  
% 2.53/1.00  --abstr_ref                             []
% 2.53/1.00  --abstr_ref_prep                        false
% 2.53/1.00  --abstr_ref_until_sat                   false
% 2.53/1.00  --abstr_ref_sig_restrict                funpre
% 2.53/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.00  --abstr_ref_under                       []
% 2.53/1.00  
% 2.53/1.00  ------ SAT Options
% 2.53/1.00  
% 2.53/1.00  --sat_mode                              false
% 2.53/1.00  --sat_fm_restart_options                ""
% 2.53/1.00  --sat_gr_def                            false
% 2.53/1.00  --sat_epr_types                         true
% 2.53/1.00  --sat_non_cyclic_types                  false
% 2.53/1.00  --sat_finite_models                     false
% 2.53/1.00  --sat_fm_lemmas                         false
% 2.53/1.00  --sat_fm_prep                           false
% 2.53/1.00  --sat_fm_uc_incr                        true
% 2.53/1.00  --sat_out_model                         small
% 2.53/1.00  --sat_out_clauses                       false
% 2.53/1.00  
% 2.53/1.00  ------ QBF Options
% 2.53/1.00  
% 2.53/1.00  --qbf_mode                              false
% 2.53/1.00  --qbf_elim_univ                         false
% 2.53/1.00  --qbf_dom_inst                          none
% 2.53/1.00  --qbf_dom_pre_inst                      false
% 2.53/1.00  --qbf_sk_in                             false
% 2.53/1.00  --qbf_pred_elim                         true
% 2.53/1.00  --qbf_split                             512
% 2.53/1.00  
% 2.53/1.00  ------ BMC1 Options
% 2.53/1.00  
% 2.53/1.00  --bmc1_incremental                      false
% 2.53/1.00  --bmc1_axioms                           reachable_all
% 2.53/1.00  --bmc1_min_bound                        0
% 2.53/1.00  --bmc1_max_bound                        -1
% 2.53/1.00  --bmc1_max_bound_default                -1
% 2.53/1.00  --bmc1_symbol_reachability              true
% 2.53/1.00  --bmc1_property_lemmas                  false
% 2.53/1.00  --bmc1_k_induction                      false
% 2.53/1.00  --bmc1_non_equiv_states                 false
% 2.53/1.00  --bmc1_deadlock                         false
% 2.53/1.00  --bmc1_ucm                              false
% 2.53/1.00  --bmc1_add_unsat_core                   none
% 2.53/1.00  --bmc1_unsat_core_children              false
% 2.53/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.00  --bmc1_out_stat                         full
% 2.53/1.00  --bmc1_ground_init                      false
% 2.53/1.00  --bmc1_pre_inst_next_state              false
% 2.53/1.00  --bmc1_pre_inst_state                   false
% 2.53/1.00  --bmc1_pre_inst_reach_state             false
% 2.53/1.00  --bmc1_out_unsat_core                   false
% 2.53/1.00  --bmc1_aig_witness_out                  false
% 2.53/1.00  --bmc1_verbose                          false
% 2.53/1.00  --bmc1_dump_clauses_tptp                false
% 2.53/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.00  --bmc1_dump_file                        -
% 2.53/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.00  --bmc1_ucm_extend_mode                  1
% 2.53/1.00  --bmc1_ucm_init_mode                    2
% 2.53/1.00  --bmc1_ucm_cone_mode                    none
% 2.53/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.00  --bmc1_ucm_relax_model                  4
% 2.53/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.00  --bmc1_ucm_layered_model                none
% 2.53/1.00  --bmc1_ucm_max_lemma_size               10
% 2.53/1.00  
% 2.53/1.00  ------ AIG Options
% 2.53/1.00  
% 2.53/1.00  --aig_mode                              false
% 2.53/1.00  
% 2.53/1.00  ------ Instantiation Options
% 2.53/1.00  
% 2.53/1.00  --instantiation_flag                    true
% 2.53/1.00  --inst_sos_flag                         false
% 2.53/1.00  --inst_sos_phase                        true
% 2.53/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.00  --inst_lit_sel_side                     num_symb
% 2.53/1.00  --inst_solver_per_active                1400
% 2.53/1.00  --inst_solver_calls_frac                1.
% 2.53/1.00  --inst_passive_queue_type               priority_queues
% 2.53/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.00  --inst_passive_queues_freq              [25;2]
% 2.53/1.00  --inst_dismatching                      true
% 2.53/1.00  --inst_eager_unprocessed_to_passive     true
% 2.53/1.00  --inst_prop_sim_given                   true
% 2.53/1.00  --inst_prop_sim_new                     false
% 2.53/1.00  --inst_subs_new                         false
% 2.53/1.00  --inst_eq_res_simp                      false
% 2.53/1.00  --inst_subs_given                       false
% 2.53/1.00  --inst_orphan_elimination               true
% 2.53/1.00  --inst_learning_loop_flag               true
% 2.53/1.00  --inst_learning_start                   3000
% 2.53/1.00  --inst_learning_factor                  2
% 2.53/1.00  --inst_start_prop_sim_after_learn       3
% 2.53/1.00  --inst_sel_renew                        solver
% 2.53/1.00  --inst_lit_activity_flag                true
% 2.53/1.00  --inst_restr_to_given                   false
% 2.53/1.00  --inst_activity_threshold               500
% 2.53/1.00  --inst_out_proof                        true
% 2.53/1.00  
% 2.53/1.00  ------ Resolution Options
% 2.53/1.00  
% 2.53/1.00  --resolution_flag                       true
% 2.53/1.00  --res_lit_sel                           adaptive
% 2.53/1.00  --res_lit_sel_side                      none
% 2.53/1.00  --res_ordering                          kbo
% 2.53/1.00  --res_to_prop_solver                    active
% 2.53/1.00  --res_prop_simpl_new                    false
% 2.53/1.00  --res_prop_simpl_given                  true
% 2.53/1.00  --res_passive_queue_type                priority_queues
% 2.53/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.00  --res_passive_queues_freq               [15;5]
% 2.53/1.00  --res_forward_subs                      full
% 2.53/1.00  --res_backward_subs                     full
% 2.53/1.00  --res_forward_subs_resolution           true
% 2.53/1.00  --res_backward_subs_resolution          true
% 2.53/1.00  --res_orphan_elimination                true
% 2.53/1.00  --res_time_limit                        2.
% 2.53/1.00  --res_out_proof                         true
% 2.53/1.00  
% 2.53/1.00  ------ Superposition Options
% 2.53/1.00  
% 2.53/1.00  --superposition_flag                    true
% 2.53/1.00  --sup_passive_queue_type                priority_queues
% 2.53/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.00  --demod_completeness_check              fast
% 2.53/1.00  --demod_use_ground                      true
% 2.53/1.00  --sup_to_prop_solver                    passive
% 2.53/1.00  --sup_prop_simpl_new                    true
% 2.53/1.00  --sup_prop_simpl_given                  true
% 2.53/1.00  --sup_fun_splitting                     false
% 2.53/1.00  --sup_smt_interval                      50000
% 2.53/1.00  
% 2.53/1.00  ------ Superposition Simplification Setup
% 2.53/1.00  
% 2.53/1.00  --sup_indices_passive                   []
% 2.53/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_full_bw                           [BwDemod]
% 2.53/1.00  --sup_immed_triv                        [TrivRules]
% 2.53/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_immed_bw_main                     []
% 2.53/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.00  
% 2.53/1.00  ------ Combination Options
% 2.53/1.00  
% 2.53/1.00  --comb_res_mult                         3
% 2.53/1.00  --comb_sup_mult                         2
% 2.53/1.00  --comb_inst_mult                        10
% 2.53/1.00  
% 2.53/1.00  ------ Debug Options
% 2.53/1.00  
% 2.53/1.00  --dbg_backtrace                         false
% 2.53/1.00  --dbg_dump_prop_clauses                 false
% 2.53/1.00  --dbg_dump_prop_clauses_file            -
% 2.53/1.00  --dbg_out_stat                          false
% 2.53/1.00  ------ Parsing...
% 2.53/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.53/1.00  ------ Proving...
% 2.53/1.00  ------ Problem Properties 
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  clauses                                 39
% 2.53/1.00  conjectures                             24
% 2.53/1.00  EPR                                     17
% 2.53/1.00  Horn                                    24
% 2.53/1.00  unary                                   23
% 2.53/1.00  binary                                  0
% 2.53/1.00  lits                                    304
% 2.53/1.00  lits eq                                 1
% 2.53/1.00  fd_pure                                 0
% 2.53/1.00  fd_pseudo                               0
% 2.53/1.00  fd_cond                                 0
% 2.53/1.00  fd_pseudo_cond                          0
% 2.53/1.00  AC symbols                              0
% 2.53/1.00  
% 2.53/1.00  ------ Schedule dynamic 5 is on 
% 2.53/1.00  
% 2.53/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  ------ 
% 2.53/1.00  Current options:
% 2.53/1.00  ------ 
% 2.53/1.00  
% 2.53/1.00  ------ Input Options
% 2.53/1.00  
% 2.53/1.00  --out_options                           all
% 2.53/1.00  --tptp_safe_out                         true
% 2.53/1.00  --problem_path                          ""
% 2.53/1.00  --include_path                          ""
% 2.53/1.00  --clausifier                            res/vclausify_rel
% 2.53/1.00  --clausifier_options                    --mode clausify
% 2.53/1.00  --stdin                                 false
% 2.53/1.00  --stats_out                             all
% 2.53/1.00  
% 2.53/1.00  ------ General Options
% 2.53/1.00  
% 2.53/1.00  --fof                                   false
% 2.53/1.00  --time_out_real                         305.
% 2.53/1.00  --time_out_virtual                      -1.
% 2.53/1.00  --symbol_type_check                     false
% 2.53/1.00  --clausify_out                          false
% 2.53/1.00  --sig_cnt_out                           false
% 2.53/1.00  --trig_cnt_out                          false
% 2.53/1.00  --trig_cnt_out_tolerance                1.
% 2.53/1.00  --trig_cnt_out_sk_spl                   false
% 2.53/1.00  --abstr_cl_out                          false
% 2.53/1.00  
% 2.53/1.00  ------ Global Options
% 2.53/1.00  
% 2.53/1.00  --schedule                              default
% 2.53/1.00  --add_important_lit                     false
% 2.53/1.00  --prop_solver_per_cl                    1000
% 2.53/1.00  --min_unsat_core                        false
% 2.53/1.00  --soft_assumptions                      false
% 2.53/1.00  --soft_lemma_size                       3
% 2.53/1.00  --prop_impl_unit_size                   0
% 2.53/1.00  --prop_impl_unit                        []
% 2.53/1.00  --share_sel_clauses                     true
% 2.53/1.00  --reset_solvers                         false
% 2.53/1.00  --bc_imp_inh                            [conj_cone]
% 2.53/1.00  --conj_cone_tolerance                   3.
% 2.53/1.00  --extra_neg_conj                        none
% 2.53/1.00  --large_theory_mode                     true
% 2.53/1.00  --prolific_symb_bound                   200
% 2.53/1.00  --lt_threshold                          2000
% 2.53/1.00  --clause_weak_htbl                      true
% 2.53/1.00  --gc_record_bc_elim                     false
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing Options
% 2.53/1.00  
% 2.53/1.00  --preprocessing_flag                    true
% 2.53/1.00  --time_out_prep_mult                    0.1
% 2.53/1.00  --splitting_mode                        input
% 2.53/1.00  --splitting_grd                         true
% 2.53/1.00  --splitting_cvd                         false
% 2.53/1.00  --splitting_cvd_svl                     false
% 2.53/1.00  --splitting_nvd                         32
% 2.53/1.00  --sub_typing                            true
% 2.53/1.00  --prep_gs_sim                           true
% 2.53/1.00  --prep_unflatten                        true
% 2.53/1.00  --prep_res_sim                          true
% 2.53/1.00  --prep_upred                            true
% 2.53/1.00  --prep_sem_filter                       exhaustive
% 2.53/1.00  --prep_sem_filter_out                   false
% 2.53/1.00  --pred_elim                             true
% 2.53/1.00  --res_sim_input                         true
% 2.53/1.00  --eq_ax_congr_red                       true
% 2.53/1.00  --pure_diseq_elim                       true
% 2.53/1.00  --brand_transform                       false
% 2.53/1.00  --non_eq_to_eq                          false
% 2.53/1.00  --prep_def_merge                        true
% 2.53/1.00  --prep_def_merge_prop_impl              false
% 2.53/1.00  --prep_def_merge_mbd                    true
% 2.53/1.00  --prep_def_merge_tr_red                 false
% 2.53/1.00  --prep_def_merge_tr_cl                  false
% 2.53/1.00  --smt_preprocessing                     true
% 2.53/1.00  --smt_ac_axioms                         fast
% 2.53/1.00  --preprocessed_out                      false
% 2.53/1.00  --preprocessed_stats                    false
% 2.53/1.00  
% 2.53/1.00  ------ Abstraction refinement Options
% 2.53/1.00  
% 2.53/1.00  --abstr_ref                             []
% 2.53/1.00  --abstr_ref_prep                        false
% 2.53/1.00  --abstr_ref_until_sat                   false
% 2.53/1.00  --abstr_ref_sig_restrict                funpre
% 2.53/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.00  --abstr_ref_under                       []
% 2.53/1.00  
% 2.53/1.00  ------ SAT Options
% 2.53/1.00  
% 2.53/1.00  --sat_mode                              false
% 2.53/1.00  --sat_fm_restart_options                ""
% 2.53/1.00  --sat_gr_def                            false
% 2.53/1.00  --sat_epr_types                         true
% 2.53/1.00  --sat_non_cyclic_types                  false
% 2.53/1.00  --sat_finite_models                     false
% 2.53/1.00  --sat_fm_lemmas                         false
% 2.53/1.00  --sat_fm_prep                           false
% 2.53/1.00  --sat_fm_uc_incr                        true
% 2.53/1.00  --sat_out_model                         small
% 2.53/1.00  --sat_out_clauses                       false
% 2.53/1.00  
% 2.53/1.00  ------ QBF Options
% 2.53/1.00  
% 2.53/1.00  --qbf_mode                              false
% 2.53/1.00  --qbf_elim_univ                         false
% 2.53/1.00  --qbf_dom_inst                          none
% 2.53/1.00  --qbf_dom_pre_inst                      false
% 2.53/1.00  --qbf_sk_in                             false
% 2.53/1.00  --qbf_pred_elim                         true
% 2.53/1.00  --qbf_split                             512
% 2.53/1.00  
% 2.53/1.00  ------ BMC1 Options
% 2.53/1.00  
% 2.53/1.00  --bmc1_incremental                      false
% 2.53/1.00  --bmc1_axioms                           reachable_all
% 2.53/1.00  --bmc1_min_bound                        0
% 2.53/1.00  --bmc1_max_bound                        -1
% 2.53/1.00  --bmc1_max_bound_default                -1
% 2.53/1.00  --bmc1_symbol_reachability              true
% 2.53/1.00  --bmc1_property_lemmas                  false
% 2.53/1.00  --bmc1_k_induction                      false
% 2.53/1.00  --bmc1_non_equiv_states                 false
% 2.53/1.00  --bmc1_deadlock                         false
% 2.53/1.00  --bmc1_ucm                              false
% 2.53/1.00  --bmc1_add_unsat_core                   none
% 2.53/1.00  --bmc1_unsat_core_children              false
% 2.53/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.00  --bmc1_out_stat                         full
% 2.53/1.00  --bmc1_ground_init                      false
% 2.53/1.00  --bmc1_pre_inst_next_state              false
% 2.53/1.00  --bmc1_pre_inst_state                   false
% 2.53/1.00  --bmc1_pre_inst_reach_state             false
% 2.53/1.00  --bmc1_out_unsat_core                   false
% 2.53/1.00  --bmc1_aig_witness_out                  false
% 2.53/1.00  --bmc1_verbose                          false
% 2.53/1.00  --bmc1_dump_clauses_tptp                false
% 2.53/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.00  --bmc1_dump_file                        -
% 2.53/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.00  --bmc1_ucm_extend_mode                  1
% 2.53/1.00  --bmc1_ucm_init_mode                    2
% 2.53/1.00  --bmc1_ucm_cone_mode                    none
% 2.53/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.00  --bmc1_ucm_relax_model                  4
% 2.53/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.00  --bmc1_ucm_layered_model                none
% 2.53/1.00  --bmc1_ucm_max_lemma_size               10
% 2.53/1.00  
% 2.53/1.00  ------ AIG Options
% 2.53/1.00  
% 2.53/1.00  --aig_mode                              false
% 2.53/1.00  
% 2.53/1.00  ------ Instantiation Options
% 2.53/1.00  
% 2.53/1.00  --instantiation_flag                    true
% 2.53/1.00  --inst_sos_flag                         false
% 2.53/1.00  --inst_sos_phase                        true
% 2.53/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.00  --inst_lit_sel_side                     none
% 2.53/1.00  --inst_solver_per_active                1400
% 2.53/1.00  --inst_solver_calls_frac                1.
% 2.53/1.00  --inst_passive_queue_type               priority_queues
% 2.53/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.00  --inst_passive_queues_freq              [25;2]
% 2.53/1.00  --inst_dismatching                      true
% 2.53/1.00  --inst_eager_unprocessed_to_passive     true
% 2.53/1.00  --inst_prop_sim_given                   true
% 2.53/1.00  --inst_prop_sim_new                     false
% 2.53/1.00  --inst_subs_new                         false
% 2.53/1.00  --inst_eq_res_simp                      false
% 2.53/1.00  --inst_subs_given                       false
% 2.53/1.00  --inst_orphan_elimination               true
% 2.53/1.00  --inst_learning_loop_flag               true
% 2.53/1.00  --inst_learning_start                   3000
% 2.53/1.00  --inst_learning_factor                  2
% 2.53/1.00  --inst_start_prop_sim_after_learn       3
% 2.53/1.00  --inst_sel_renew                        solver
% 2.53/1.00  --inst_lit_activity_flag                true
% 2.53/1.00  --inst_restr_to_given                   false
% 2.53/1.00  --inst_activity_threshold               500
% 2.53/1.00  --inst_out_proof                        true
% 2.53/1.00  
% 2.53/1.00  ------ Resolution Options
% 2.53/1.00  
% 2.53/1.00  --resolution_flag                       false
% 2.53/1.00  --res_lit_sel                           adaptive
% 2.53/1.00  --res_lit_sel_side                      none
% 2.53/1.00  --res_ordering                          kbo
% 2.53/1.00  --res_to_prop_solver                    active
% 2.53/1.00  --res_prop_simpl_new                    false
% 2.53/1.00  --res_prop_simpl_given                  true
% 2.53/1.00  --res_passive_queue_type                priority_queues
% 2.53/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.00  --res_passive_queues_freq               [15;5]
% 2.53/1.00  --res_forward_subs                      full
% 2.53/1.00  --res_backward_subs                     full
% 2.53/1.00  --res_forward_subs_resolution           true
% 2.53/1.00  --res_backward_subs_resolution          true
% 2.53/1.00  --res_orphan_elimination                true
% 2.53/1.00  --res_time_limit                        2.
% 2.53/1.00  --res_out_proof                         true
% 2.53/1.00  
% 2.53/1.00  ------ Superposition Options
% 2.53/1.00  
% 2.53/1.00  --superposition_flag                    true
% 2.53/1.00  --sup_passive_queue_type                priority_queues
% 2.53/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.00  --demod_completeness_check              fast
% 2.53/1.00  --demod_use_ground                      true
% 2.53/1.00  --sup_to_prop_solver                    passive
% 2.53/1.00  --sup_prop_simpl_new                    true
% 2.53/1.00  --sup_prop_simpl_given                  true
% 2.53/1.00  --sup_fun_splitting                     false
% 2.53/1.00  --sup_smt_interval                      50000
% 2.53/1.00  
% 2.53/1.00  ------ Superposition Simplification Setup
% 2.53/1.00  
% 2.53/1.00  --sup_indices_passive                   []
% 2.53/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_full_bw                           [BwDemod]
% 2.53/1.00  --sup_immed_triv                        [TrivRules]
% 2.53/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_immed_bw_main                     []
% 2.53/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.00  
% 2.53/1.00  ------ Combination Options
% 2.53/1.00  
% 2.53/1.00  --comb_res_mult                         3
% 2.53/1.00  --comb_sup_mult                         2
% 2.53/1.00  --comb_inst_mult                        10
% 2.53/1.00  
% 2.53/1.00  ------ Debug Options
% 2.53/1.00  
% 2.53/1.00  --dbg_backtrace                         false
% 2.53/1.00  --dbg_dump_prop_clauses                 false
% 2.53/1.00  --dbg_dump_prop_clauses_file            -
% 2.53/1.00  --dbg_out_stat                          false
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  ------ Proving...
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  % SZS status Theorem for theBenchmark.p
% 2.53/1.00  
% 2.53/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.53/1.00  
% 2.53/1.00  fof(f6,conjecture,(
% 2.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f7,negated_conjecture,(
% 2.53/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 2.53/1.00    inference(negated_conjecture,[],[f6])).
% 2.53/1.00  
% 2.53/1.00  fof(f18,plain,(
% 2.53/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f7])).
% 2.53/1.00  
% 2.53/1.00  fof(f19,plain,(
% 2.53/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f18])).
% 2.53/1.00  
% 2.53/1.00  fof(f27,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,sK5)),sK5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,sK5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(sK5,X3,X1) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.53/1.00    introduced(choice_axiom,[])).
% 2.53/1.00  
% 2.53/1.00  fof(f26,plain,(
% 2.53/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,sK4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,sK4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,sK4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,sK4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,sK4,X5)),sK4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(sK4,X2,X1) & v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.53/1.00    introduced(choice_axiom,[])).
% 2.53/1.00  
% 2.53/1.00  fof(f25,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,sK3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,sK3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,sK3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,sK3,X4,X5))) & r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK3),sK3,k10_tmap_1(X0,X1,X2,sK3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK3),X2,k10_tmap_1(X0,X1,X2,sK3,X4,X5)),X4) & k1_tsep_1(X0,X2,sK3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v5_pre_topc(X5,sK3,X1) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & v1_borsuk_1(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.53/1.00    introduced(choice_axiom,[])).
% 2.53/1.00  
% 2.53/1.00  fof(f24,plain,(
% 2.53/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,sK2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,sK2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,sK2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,sK2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK2,X3),X3,k10_tmap_1(X0,X1,sK2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK2,X3),sK2,k10_tmap_1(X0,X1,sK2,X3,X4,X5)),X4) & k1_tsep_1(X0,sK2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X4,sK2,X1) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & v1_borsuk_1(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.53/1.00    introduced(choice_axiom,[])).
% 2.53/1.00  
% 2.53/1.00  fof(f23,plain,(
% 2.53/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,sK1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(X0,sK1,X2,X3,X4,X5),X0,sK1) | ~v1_funct_2(k10_tmap_1(X0,sK1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(X0,sK1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(sK1),k3_tmap_1(X0,sK1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,sK1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,sK1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(X5,X3,sK1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v5_pre_topc(X4,X2,sK1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.53/1.00    introduced(choice_axiom,[])).
% 2.53/1.00  
% 2.53/1.00  fof(f22,plain,(
% 2.53/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK0,X1,X2,X3,X4,X5),sK0,X1) | ~v1_funct_2(k10_tmap_1(sK0,X1,X2,X3,X4,X5),u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X3,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,k1_tsep_1(sK0,X2,X3),X2,k10_tmap_1(sK0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(sK0,X2,X3) = sK0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & v1_borsuk_1(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.53/1.00    introduced(choice_axiom,[])).
% 2.53/1.00  
% 2.53/1.00  fof(f28,plain,(
% 2.53/1.00    ((((((~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) & r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) & r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) & k1_tsep_1(sK0,sK2,sK3) = sK0 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(sK5,sK3,sK1) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v5_pre_topc(sK4,sK2,sK1) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & v1_borsuk_1(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & v1_borsuk_1(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f19,f27,f26,f25,f24,f23,f22])).
% 2.53/1.00  
% 2.53/1.00  fof(f66,plain,(
% 2.53/1.00    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f64,plain,(
% 2.53/1.00    k1_tsep_1(sK0,sK2,sK3) = sK0),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f2,axiom,(
% 2.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))))))))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f10,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | r1_tsep_1(X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f2])).
% 2.53/1.00  
% 2.53/1.00  fof(f11,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f10])).
% 2.53/1.00  
% 2.53/1.00  fof(f20,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) & (r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | (~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(nnf_transformation,[],[f11])).
% 2.53/1.00  
% 2.53/1.00  fof(f21,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) & (r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f20])).
% 2.53/1.00  
% 2.53/1.00  fof(f32,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f21])).
% 2.53/1.00  
% 2.53/1.00  fof(f44,plain,(
% 2.53/1.00    ~v2_struct_0(sK0)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f45,plain,(
% 2.53/1.00    v2_pre_topc(sK0)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f46,plain,(
% 2.53/1.00    l1_pre_topc(sK0)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f47,plain,(
% 2.53/1.00    ~v2_struct_0(sK1)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f48,plain,(
% 2.53/1.00    v2_pre_topc(sK1)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f49,plain,(
% 2.53/1.00    l1_pre_topc(sK1)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f50,plain,(
% 2.53/1.00    ~v2_struct_0(sK2)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f52,plain,(
% 2.53/1.00    m1_pre_topc(sK2,sK0)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f53,plain,(
% 2.53/1.00    ~v2_struct_0(sK3)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f55,plain,(
% 2.53/1.00    m1_pre_topc(sK3,sK0)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f56,plain,(
% 2.53/1.00    v1_funct_1(sK4)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f57,plain,(
% 2.53/1.00    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f58,plain,(
% 2.53/1.00    v5_pre_topc(sK4,sK2,sK1)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f59,plain,(
% 2.53/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f60,plain,(
% 2.53/1.00    v1_funct_1(sK5)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f61,plain,(
% 2.53/1.00    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f62,plain,(
% 2.53/1.00    v5_pre_topc(sK5,sK3,sK1)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f63,plain,(
% 2.53/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f4,axiom,(
% 2.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => (r4_tsep_1(X0,X2,X3) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f14,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r1_tsep_1(X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f4])).
% 2.53/1.00  
% 2.53/1.00  fof(f15,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f14])).
% 2.53/1.00  
% 2.53/1.00  fof(f41,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~r4_tsep_1(X0,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f15])).
% 2.53/1.00  
% 2.53/1.00  fof(f51,plain,(
% 2.53/1.00    v1_borsuk_1(sK2,sK0)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f54,plain,(
% 2.53/1.00    v1_borsuk_1(sK3,sK0)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f5,axiom,(
% 2.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f16,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f5])).
% 2.53/1.00  
% 2.53/1.00  fof(f17,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f16])).
% 2.53/1.00  
% 2.53/1.00  fof(f43,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f17])).
% 2.53/1.00  
% 2.53/1.00  fof(f1,axiom,(
% 2.53/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f8,plain,(
% 2.53/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f1])).
% 2.53/1.00  
% 2.53/1.00  fof(f9,plain,(
% 2.53/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f8])).
% 2.53/1.00  
% 2.53/1.00  fof(f30,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f9])).
% 2.53/1.00  
% 2.53/1.00  fof(f31,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f9])).
% 2.53/1.00  
% 2.53/1.00  fof(f67,plain,(
% 2.53/1.00    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f29,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f9])).
% 2.53/1.00  
% 2.53/1.00  fof(f65,plain,(
% 2.53/1.00    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)),
% 2.53/1.00    inference(cnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f3,axiom,(
% 2.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f12,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~r4_tsep_1(X0,X2,X3) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | r1_tsep_1(X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f3])).
% 2.53/1.00  
% 2.53/1.00  fof(f13,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f12])).
% 2.53/1.00  
% 2.53/1.00  fof(f37,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~r4_tsep_1(X0,X2,X3) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f13])).
% 2.53/1.00  
% 2.53/1.00  cnf(c_16,negated_conjecture,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
% 2.53/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1251,negated_conjecture,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1972,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1251]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_18,negated_conjecture,
% 2.53/1.00      ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
% 2.53/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1249,negated_conjecture,
% 2.53/1.00      ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2039,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) = iProver_top ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_1972,c_1249]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_5,plain,
% 2.53/1.00      ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X5)
% 2.53/1.00      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X3,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X4)
% 2.53/1.00      | r2_funct_2(u1_struct_0(k2_tsep_1(X2,X3,X0)),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X3,X0),X4),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X3,X0),X5))
% 2.53/1.00      | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
% 2.53/1.00      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 2.53/1.00      | r1_tsep_1(X3,X0)
% 2.53/1.00      | ~ m1_pre_topc(X0,X2)
% 2.53/1.00      | ~ m1_pre_topc(X3,X2)
% 2.53/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.53/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.53/1.00      | ~ v2_pre_topc(X1)
% 2.53/1.00      | ~ v2_pre_topc(X2)
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | ~ l1_pre_topc(X2)
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | v2_struct_0(X3)
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | ~ v1_funct_1(X5)
% 2.53/1.00      | ~ v1_funct_1(X4) ),
% 2.53/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1259,plain,
% 2.53/1.00      ( ~ r2_funct_2(u1_struct_0(X0_55),u1_struct_0(X1_55),k3_tmap_1(X2_55,X1_55,k1_tsep_1(X2_55,X3_55,X0_55),X0_55,k10_tmap_1(X2_55,X1_55,X3_55,X0_55,X0_53,X1_53)),X1_53)
% 2.53/1.00      | ~ r2_funct_2(u1_struct_0(X3_55),u1_struct_0(X1_55),k3_tmap_1(X2_55,X1_55,k1_tsep_1(X2_55,X3_55,X0_55),X3_55,k10_tmap_1(X2_55,X1_55,X3_55,X0_55,X0_53,X1_53)),X0_53)
% 2.53/1.00      | r2_funct_2(u1_struct_0(k2_tsep_1(X2_55,X3_55,X0_55)),u1_struct_0(X1_55),k3_tmap_1(X2_55,X1_55,X3_55,k2_tsep_1(X2_55,X3_55,X0_55),X0_53),k3_tmap_1(X2_55,X1_55,X0_55,k2_tsep_1(X2_55,X3_55,X0_55),X1_53))
% 2.53/1.00      | ~ v1_funct_2(X1_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 2.53/1.00      | ~ v1_funct_2(X0_53,u1_struct_0(X3_55),u1_struct_0(X1_55))
% 2.53/1.00      | r1_tsep_1(X3_55,X0_55)
% 2.53/1.00      | ~ m1_pre_topc(X0_55,X2_55)
% 2.53/1.00      | ~ m1_pre_topc(X3_55,X2_55)
% 2.53/1.00      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 2.53/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55))))
% 2.53/1.00      | ~ v2_pre_topc(X2_55)
% 2.53/1.00      | ~ v2_pre_topc(X1_55)
% 2.53/1.00      | ~ l1_pre_topc(X2_55)
% 2.53/1.00      | ~ l1_pre_topc(X1_55)
% 2.53/1.00      | v2_struct_0(X1_55)
% 2.53/1.00      | v2_struct_0(X2_55)
% 2.53/1.00      | v2_struct_0(X0_55)
% 2.53/1.00      | v2_struct_0(X3_55)
% 2.53/1.00      | ~ v1_funct_1(X0_53)
% 2.53/1.00      | ~ v1_funct_1(X1_53) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1964,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(X0_55),u1_struct_0(X1_55),k3_tmap_1(X2_55,X1_55,k1_tsep_1(X2_55,X3_55,X0_55),X0_55,k10_tmap_1(X2_55,X1_55,X3_55,X0_55,X0_53,X1_53)),X1_53) != iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(X3_55),u1_struct_0(X1_55),k3_tmap_1(X2_55,X1_55,k1_tsep_1(X2_55,X3_55,X0_55),X3_55,k10_tmap_1(X2_55,X1_55,X3_55,X0_55,X0_53,X1_53)),X0_53) != iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(k2_tsep_1(X2_55,X3_55,X0_55)),u1_struct_0(X1_55),k3_tmap_1(X2_55,X1_55,X3_55,k2_tsep_1(X2_55,X3_55,X0_55),X0_53),k3_tmap_1(X2_55,X1_55,X0_55,k2_tsep_1(X2_55,X3_55,X0_55),X1_53)) = iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X0_53,u1_struct_0(X3_55),u1_struct_0(X1_55)) != iProver_top
% 2.53/1.00      | r1_tsep_1(X3_55,X0_55) = iProver_top
% 2.53/1.00      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 2.53/1.00      | m1_pre_topc(X3_55,X2_55) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(X2_55) != iProver_top
% 2.53/1.00      | v2_pre_topc(X1_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X2_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X1_55) != iProver_top
% 2.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X2_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X1_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X3_55) = iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1259]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4046,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK2,k2_tsep_1(sK0,sK2,sK3),X0_53),k3_tmap_1(sK0,X0_55,sK3,k2_tsep_1(sK0,sK2,sK3),X1_53)) = iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK0,sK3,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X1_53) != iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X0_53) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | r1_tsep_1(sK2,sK3) = iProver_top
% 2.53/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.53/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v2_struct_0(sK3) = iProver_top
% 2.53/1.00      | v2_struct_0(sK2) = iProver_top
% 2.53/1.00      | v2_struct_0(sK0) = iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1249,c_1964]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4047,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK2,k2_tsep_1(sK0,sK2,sK3),X0_53),k3_tmap_1(sK0,X0_55,sK3,k2_tsep_1(sK0,sK2,sK3),X1_53)) = iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK0,sK3,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X1_53) != iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK0,sK2,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X0_53) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | r1_tsep_1(sK2,sK3) = iProver_top
% 2.53/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.53/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v2_struct_0(sK3) = iProver_top
% 2.53/1.00      | v2_struct_0(sK2) = iProver_top
% 2.53/1.00      | v2_struct_0(sK0) = iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_4046,c_1249]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_38,negated_conjecture,
% 2.53/1.00      ( ~ v2_struct_0(sK0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_39,plain,
% 2.53/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_37,negated_conjecture,
% 2.53/1.00      ( v2_pre_topc(sK0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_40,plain,
% 2.53/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_36,negated_conjecture,
% 2.53/1.00      ( l1_pre_topc(sK0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_41,plain,
% 2.53/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_35,negated_conjecture,
% 2.53/1.00      ( ~ v2_struct_0(sK1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_42,plain,
% 2.53/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_34,negated_conjecture,
% 2.53/1.00      ( v2_pre_topc(sK1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_43,plain,
% 2.53/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_33,negated_conjecture,
% 2.53/1.00      ( l1_pre_topc(sK1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_44,plain,
% 2.53/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_32,negated_conjecture,
% 2.53/1.00      ( ~ v2_struct_0(sK2) ),
% 2.53/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_45,plain,
% 2.53/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_30,negated_conjecture,
% 2.53/1.00      ( m1_pre_topc(sK2,sK0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_47,plain,
% 2.53/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_29,negated_conjecture,
% 2.53/1.00      ( ~ v2_struct_0(sK3) ),
% 2.53/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_48,plain,
% 2.53/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_27,negated_conjecture,
% 2.53/1.00      ( m1_pre_topc(sK3,sK0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_50,plain,
% 2.53/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_26,negated_conjecture,
% 2.53/1.00      ( v1_funct_1(sK4) ),
% 2.53/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_51,plain,
% 2.53/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_25,negated_conjecture,
% 2.53/1.00      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 2.53/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_52,plain,
% 2.53/1.00      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_24,negated_conjecture,
% 2.53/1.00      ( v5_pre_topc(sK4,sK2,sK1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_53,plain,
% 2.53/1.00      ( v5_pre_topc(sK4,sK2,sK1) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_23,negated_conjecture,
% 2.53/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 2.53/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_54,plain,
% 2.53/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_22,negated_conjecture,
% 2.53/1.00      ( v1_funct_1(sK5) ),
% 2.53/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_55,plain,
% 2.53/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_21,negated_conjecture,
% 2.53/1.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 2.53/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_56,plain,
% 2.53/1.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_20,negated_conjecture,
% 2.53/1.00      ( v5_pre_topc(sK5,sK3,sK1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_57,plain,
% 2.53/1.00      ( v5_pre_topc(sK5,sK3,sK1) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_19,negated_conjecture,
% 2.53/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.53/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_58,plain,
% 2.53/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_11,plain,
% 2.53/1.00      ( ~ v5_pre_topc(X0,X1,X2)
% 2.53/1.00      | ~ v5_pre_topc(X3,X4,X2)
% 2.53/1.00      | v5_pre_topc(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_tsep_1(X5,X4,X1),X2)
% 2.53/1.00      | ~ r4_tsep_1(X5,X4,X1)
% 2.53/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.53/1.00      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 2.53/1.00      | ~ r1_tsep_1(X4,X1)
% 2.53/1.00      | ~ m1_pre_topc(X1,X5)
% 2.53/1.00      | ~ m1_pre_topc(X4,X5)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.53/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 2.53/1.00      | ~ v2_pre_topc(X2)
% 2.53/1.00      | ~ v2_pre_topc(X5)
% 2.53/1.00      | ~ l1_pre_topc(X2)
% 2.53/1.00      | ~ l1_pre_topc(X5)
% 2.53/1.00      | v2_struct_0(X5)
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | v2_struct_0(X4)
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ v1_funct_1(X0)
% 2.53/1.00      | ~ v1_funct_1(X3) ),
% 2.53/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1254,plain,
% 2.53/1.00      ( ~ v5_pre_topc(X0_53,X0_55,X1_55)
% 2.53/1.00      | ~ v5_pre_topc(X1_53,X2_55,X1_55)
% 2.53/1.00      | v5_pre_topc(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),k1_tsep_1(X3_55,X2_55,X0_55),X1_55)
% 2.53/1.00      | ~ r4_tsep_1(X3_55,X2_55,X0_55)
% 2.53/1.00      | ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 2.53/1.00      | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
% 2.53/1.00      | ~ r1_tsep_1(X2_55,X0_55)
% 2.53/1.00      | ~ m1_pre_topc(X0_55,X3_55)
% 2.53/1.00      | ~ m1_pre_topc(X2_55,X3_55)
% 2.53/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 2.53/1.00      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 2.53/1.00      | ~ v2_pre_topc(X1_55)
% 2.53/1.00      | ~ v2_pre_topc(X3_55)
% 2.53/1.00      | ~ l1_pre_topc(X1_55)
% 2.53/1.00      | ~ l1_pre_topc(X3_55)
% 2.53/1.00      | v2_struct_0(X1_55)
% 2.53/1.00      | v2_struct_0(X2_55)
% 2.53/1.00      | v2_struct_0(X0_55)
% 2.53/1.00      | v2_struct_0(X3_55)
% 2.53/1.00      | ~ v1_funct_1(X0_53)
% 2.53/1.00      | ~ v1_funct_1(X1_53) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1969,plain,
% 2.53/1.00      ( v5_pre_topc(X0_53,X0_55,X1_55) != iProver_top
% 2.53/1.00      | v5_pre_topc(X1_53,X2_55,X1_55) != iProver_top
% 2.53/1.00      | v5_pre_topc(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),k1_tsep_1(X3_55,X2_55,X0_55),X1_55) = iProver_top
% 2.53/1.00      | r4_tsep_1(X3_55,X2_55,X0_55) != iProver_top
% 2.53/1.00      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
% 2.53/1.00      | r1_tsep_1(X2_55,X0_55) != iProver_top
% 2.53/1.00      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 2.53/1.00      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(X3_55) != iProver_top
% 2.53/1.00      | v2_pre_topc(X1_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X3_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X1_55) != iProver_top
% 2.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X2_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X1_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X3_55) = iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1254]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3948,plain,
% 2.53/1.00      ( v5_pre_topc(X0_53,sK3,X0_55) != iProver_top
% 2.53/1.00      | v5_pre_topc(X1_53,sK2,X0_55) != iProver_top
% 2.53/1.00      | v5_pre_topc(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),sK0,X0_55) = iProver_top
% 2.53/1.00      | r4_tsep_1(sK0,sK2,sK3) != iProver_top
% 2.53/1.00      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | r1_tsep_1(sK2,sK3) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.53/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v2_struct_0(sK3) = iProver_top
% 2.53/1.00      | v2_struct_0(sK2) = iProver_top
% 2.53/1.00      | v2_struct_0(sK0) = iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1249,c_1969]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_31,negated_conjecture,
% 2.53/1.00      ( v1_borsuk_1(sK2,sK0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_46,plain,
% 2.53/1.00      ( v1_borsuk_1(sK2,sK0) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_28,negated_conjecture,
% 2.53/1.00      ( v1_borsuk_1(sK3,sK0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_49,plain,
% 2.53/1.00      ( v1_borsuk_1(sK3,sK0) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_14,plain,
% 2.53/1.00      ( r4_tsep_1(X0,X1,X2)
% 2.53/1.00      | ~ v1_borsuk_1(X2,X0)
% 2.53/1.00      | ~ v1_borsuk_1(X1,X0)
% 2.53/1.00      | ~ m1_pre_topc(X2,X0)
% 2.53/1.00      | ~ m1_pre_topc(X1,X0)
% 2.53/1.00      | ~ v2_pre_topc(X0)
% 2.53/1.00      | ~ l1_pre_topc(X0)
% 2.53/1.00      | v2_struct_0(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1253,plain,
% 2.53/1.00      ( r4_tsep_1(X0_55,X1_55,X2_55)
% 2.53/1.00      | ~ v1_borsuk_1(X2_55,X0_55)
% 2.53/1.00      | ~ v1_borsuk_1(X1_55,X0_55)
% 2.53/1.00      | ~ m1_pre_topc(X2_55,X0_55)
% 2.53/1.00      | ~ m1_pre_topc(X1_55,X0_55)
% 2.53/1.00      | ~ v2_pre_topc(X0_55)
% 2.53/1.00      | ~ l1_pre_topc(X0_55)
% 2.53/1.00      | v2_struct_0(X0_55) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2522,plain,
% 2.53/1.00      ( r4_tsep_1(sK0,X0_55,sK3)
% 2.53/1.00      | ~ v1_borsuk_1(X0_55,sK0)
% 2.53/1.00      | ~ v1_borsuk_1(sK3,sK0)
% 2.53/1.00      | ~ m1_pre_topc(X0_55,sK0)
% 2.53/1.00      | ~ m1_pre_topc(sK3,sK0)
% 2.53/1.00      | ~ v2_pre_topc(sK0)
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | v2_struct_0(sK0) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_1253]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2681,plain,
% 2.53/1.00      ( r4_tsep_1(sK0,sK2,sK3)
% 2.53/1.00      | ~ v1_borsuk_1(sK3,sK0)
% 2.53/1.00      | ~ v1_borsuk_1(sK2,sK0)
% 2.53/1.00      | ~ m1_pre_topc(sK3,sK0)
% 2.53/1.00      | ~ m1_pre_topc(sK2,sK0)
% 2.53/1.00      | ~ v2_pre_topc(sK0)
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | v2_struct_0(sK0) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_2522]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2682,plain,
% 2.53/1.00      ( r4_tsep_1(sK0,sK2,sK3) = iProver_top
% 2.53/1.00      | v1_borsuk_1(sK3,sK0) != iProver_top
% 2.53/1.00      | v1_borsuk_1(sK2,sK0) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.53/1.00      | v2_struct_0(sK0) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2681]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3969,plain,
% 2.53/1.00      ( v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | r1_tsep_1(sK2,sK3) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v5_pre_topc(X0_53,sK3,X0_55) != iProver_top
% 2.53/1.00      | v5_pre_topc(X1_53,sK2,X0_55) != iProver_top
% 2.53/1.00      | v5_pre_topc(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),sK0,X0_55) = iProver_top
% 2.53/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_3948,c_39,c_40,c_41,c_45,c_46,c_47,c_48,c_49,c_50,
% 2.53/1.00                 c_2682]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3970,plain,
% 2.53/1.00      ( v5_pre_topc(X0_53,sK3,X0_55) != iProver_top
% 2.53/1.00      | v5_pre_topc(X1_53,sK2,X0_55) != iProver_top
% 2.53/1.00      | v5_pre_topc(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),sK0,X0_55) = iProver_top
% 2.53/1.00      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | r1_tsep_1(sK2,sK3) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_3969]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1,plain,
% 2.53/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.53/1.00      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 2.53/1.00      | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
% 2.53/1.00      | ~ m1_pre_topc(X1,X5)
% 2.53/1.00      | ~ m1_pre_topc(X4,X5)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.53/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 2.53/1.00      | ~ v2_pre_topc(X2)
% 2.53/1.00      | ~ v2_pre_topc(X5)
% 2.53/1.00      | ~ l1_pre_topc(X2)
% 2.53/1.00      | ~ l1_pre_topc(X5)
% 2.53/1.00      | v2_struct_0(X5)
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | v2_struct_0(X4)
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ v1_funct_1(X0)
% 2.53/1.00      | ~ v1_funct_1(X3) ),
% 2.53/1.00      inference(cnf_transformation,[],[f30]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1263,plain,
% 2.53/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 2.53/1.00      | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
% 2.53/1.00      | v1_funct_2(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))
% 2.53/1.00      | ~ m1_pre_topc(X0_55,X3_55)
% 2.53/1.00      | ~ m1_pre_topc(X2_55,X3_55)
% 2.53/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 2.53/1.00      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 2.53/1.00      | ~ v2_pre_topc(X1_55)
% 2.53/1.00      | ~ v2_pre_topc(X3_55)
% 2.53/1.00      | ~ l1_pre_topc(X1_55)
% 2.53/1.00      | ~ l1_pre_topc(X3_55)
% 2.53/1.00      | v2_struct_0(X1_55)
% 2.53/1.00      | v2_struct_0(X2_55)
% 2.53/1.00      | v2_struct_0(X0_55)
% 2.53/1.00      | v2_struct_0(X3_55)
% 2.53/1.00      | ~ v1_funct_1(X0_53)
% 2.53/1.00      | ~ v1_funct_1(X1_53) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1960,plain,
% 2.53/1.00      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55)) = iProver_top
% 2.53/1.00      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 2.53/1.00      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(X3_55) != iProver_top
% 2.53/1.00      | v2_pre_topc(X1_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X3_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X1_55) != iProver_top
% 2.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X2_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X1_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X3_55) = iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1263]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3070,plain,
% 2.53/1.00      ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),u1_struct_0(sK0),u1_struct_0(X0_55)) = iProver_top
% 2.53/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.53/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v2_struct_0(sK3) = iProver_top
% 2.53/1.00      | v2_struct_0(sK2) = iProver_top
% 2.53/1.00      | v2_struct_0(sK0) = iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1249,c_1960]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3289,plain,
% 2.53/1.00      ( v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | v1_funct_2(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),u1_struct_0(sK0),u1_struct_0(X0_55)) = iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_3070,c_39,c_40,c_41,c_45,c_47,c_48,c_50]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3290,plain,
% 2.53/1.00      ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),u1_struct_0(sK0),u1_struct_0(X0_55)) = iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_3289]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_0,plain,
% 2.53/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.53/1.00      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 2.53/1.00      | ~ m1_pre_topc(X1,X5)
% 2.53/1.00      | ~ m1_pre_topc(X4,X5)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.53/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 2.53/1.00      | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
% 2.53/1.00      | ~ v2_pre_topc(X2)
% 2.53/1.00      | ~ v2_pre_topc(X5)
% 2.53/1.00      | ~ l1_pre_topc(X2)
% 2.53/1.00      | ~ l1_pre_topc(X5)
% 2.53/1.00      | v2_struct_0(X5)
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | v2_struct_0(X4)
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ v1_funct_1(X0)
% 2.53/1.00      | ~ v1_funct_1(X3) ),
% 2.53/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1264,plain,
% 2.53/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 2.53/1.00      | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
% 2.53/1.00      | ~ m1_pre_topc(X0_55,X3_55)
% 2.53/1.00      | ~ m1_pre_topc(X2_55,X3_55)
% 2.53/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 2.53/1.00      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 2.53/1.00      | m1_subset_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))))
% 2.53/1.00      | ~ v2_pre_topc(X1_55)
% 2.53/1.00      | ~ v2_pre_topc(X3_55)
% 2.53/1.00      | ~ l1_pre_topc(X1_55)
% 2.53/1.00      | ~ l1_pre_topc(X3_55)
% 2.53/1.00      | v2_struct_0(X1_55)
% 2.53/1.00      | v2_struct_0(X2_55)
% 2.53/1.00      | v2_struct_0(X0_55)
% 2.53/1.00      | v2_struct_0(X3_55)
% 2.53/1.00      | ~ v1_funct_1(X0_53)
% 2.53/1.00      | ~ v1_funct_1(X1_53) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1959,plain,
% 2.53/1.00      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
% 2.53/1.00      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 2.53/1.00      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55)))) = iProver_top
% 2.53/1.00      | v2_pre_topc(X3_55) != iProver_top
% 2.53/1.00      | v2_pre_topc(X1_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X3_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X1_55) != iProver_top
% 2.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X2_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X1_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X3_55) = iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1264]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2590,plain,
% 2.53/1.00      ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_55)))) = iProver_top
% 2.53/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.53/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v2_struct_0(sK3) = iProver_top
% 2.53/1.00      | v2_struct_0(sK2) = iProver_top
% 2.53/1.00      | v2_struct_0(sK0) = iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_1249,c_1959]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3354,plain,
% 2.53/1.00      ( v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | m1_subset_1(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_55)))) = iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_2590,c_39,c_40,c_41,c_45,c_47,c_48,c_50]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3355,plain,
% 2.53/1.00      ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_55)))) = iProver_top
% 2.53/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_3354]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_15,negated_conjecture,
% 2.53/1.00      ( ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
% 2.53/1.00      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.53/1.00      | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.53/1.00      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
% 2.53/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1252,negated_conjecture,
% 2.53/1.00      ( ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
% 2.53/1.00      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.53/1.00      | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.53/1.00      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1971,plain,
% 2.53/1.00      ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top
% 2.53/1.00      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1252]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_61,plain,
% 2.53/1.00      ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top
% 2.53/1.00      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2,plain,
% 2.53/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.53/1.00      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 2.53/1.00      | ~ m1_pre_topc(X1,X5)
% 2.53/1.00      | ~ m1_pre_topc(X4,X5)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.53/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 2.53/1.00      | ~ v2_pre_topc(X2)
% 2.53/1.00      | ~ v2_pre_topc(X5)
% 2.53/1.00      | ~ l1_pre_topc(X2)
% 2.53/1.00      | ~ l1_pre_topc(X5)
% 2.53/1.00      | v2_struct_0(X5)
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | v2_struct_0(X4)
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ v1_funct_1(X0)
% 2.53/1.00      | ~ v1_funct_1(X3)
% 2.53/1.00      | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
% 2.53/1.00      inference(cnf_transformation,[],[f29]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1262,plain,
% 2.53/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 2.53/1.00      | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X1_55))
% 2.53/1.00      | ~ m1_pre_topc(X0_55,X3_55)
% 2.53/1.00      | ~ m1_pre_topc(X2_55,X3_55)
% 2.53/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 2.53/1.00      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 2.53/1.00      | ~ v2_pre_topc(X1_55)
% 2.53/1.00      | ~ v2_pre_topc(X3_55)
% 2.53/1.00      | ~ l1_pre_topc(X1_55)
% 2.53/1.00      | ~ l1_pre_topc(X3_55)
% 2.53/1.00      | v2_struct_0(X1_55)
% 2.53/1.00      | v2_struct_0(X2_55)
% 2.53/1.00      | v2_struct_0(X0_55)
% 2.53/1.00      | v2_struct_0(X3_55)
% 2.53/1.00      | ~ v1_funct_1(X0_53)
% 2.53/1.00      | ~ v1_funct_1(X1_53)
% 2.53/1.00      | v1_funct_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_53,X0_53)) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2542,plain,
% 2.53/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 2.53/1.00      | ~ v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(X1_55))
% 2.53/1.00      | ~ m1_pre_topc(X0_55,sK0)
% 2.53/1.00      | ~ m1_pre_topc(sK3,sK0)
% 2.53/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 2.53/1.00      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_55))))
% 2.53/1.00      | ~ v2_pre_topc(X1_55)
% 2.53/1.00      | ~ v2_pre_topc(sK0)
% 2.53/1.00      | ~ l1_pre_topc(X1_55)
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | v2_struct_0(X0_55)
% 2.53/1.00      | v2_struct_0(X1_55)
% 2.53/1.00      | v2_struct_0(sK3)
% 2.53/1.00      | v2_struct_0(sK0)
% 2.53/1.00      | ~ v1_funct_1(X1_53)
% 2.53/1.00      | ~ v1_funct_1(X0_53)
% 2.53/1.00      | v1_funct_1(k10_tmap_1(sK0,X1_55,X0_55,sK3,X0_53,X1_53)) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_1262]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2761,plain,
% 2.53/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_55))
% 2.53/1.00      | ~ v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_55))
% 2.53/1.00      | ~ m1_pre_topc(sK3,sK0)
% 2.53/1.00      | ~ m1_pre_topc(sK2,sK0)
% 2.53/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55))))
% 2.53/1.00      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55))))
% 2.53/1.00      | ~ v2_pre_topc(X0_55)
% 2.53/1.00      | ~ v2_pre_topc(sK0)
% 2.53/1.00      | ~ l1_pre_topc(X0_55)
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | v2_struct_0(X0_55)
% 2.53/1.00      | v2_struct_0(sK3)
% 2.53/1.00      | v2_struct_0(sK2)
% 2.53/1.00      | v2_struct_0(sK0)
% 2.53/1.00      | ~ v1_funct_1(X1_53)
% 2.53/1.00      | ~ v1_funct_1(X0_53)
% 2.53/1.00      | v1_funct_1(k10_tmap_1(sK0,X0_55,sK2,sK3,X1_53,X0_53)) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_2542]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2821,plain,
% 2.53/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1))
% 2.53/1.00      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 2.53/1.00      | ~ m1_pre_topc(sK3,sK0)
% 2.53/1.00      | ~ m1_pre_topc(sK2,sK0)
% 2.53/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.53/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.53/1.00      | ~ v2_pre_topc(sK1)
% 2.53/1.00      | ~ v2_pre_topc(sK0)
% 2.53/1.00      | ~ l1_pre_topc(sK1)
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | v2_struct_0(sK3)
% 2.53/1.00      | v2_struct_0(sK2)
% 2.53/1.00      | v2_struct_0(sK1)
% 2.53/1.00      | v2_struct_0(sK0)
% 2.53/1.00      | ~ v1_funct_1(X0_53)
% 2.53/1.00      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,sK5))
% 2.53/1.00      | ~ v1_funct_1(sK5) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_2761]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2822,plain,
% 2.53/1.00      ( v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.53/1.00      | v2_struct_0(sK3) = iProver_top
% 2.53/1.00      | v2_struct_0(sK2) = iProver_top
% 2.53/1.00      | v2_struct_0(sK1) = iProver_top
% 2.53/1.00      | v2_struct_0(sK0) = iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.53/1.00      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,sK5)) = iProver_top
% 2.53/1.00      | v1_funct_1(sK5) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2821]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2824,plain,
% 2.53/1.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.53/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.53/1.00      | v2_struct_0(sK3) = iProver_top
% 2.53/1.00      | v2_struct_0(sK2) = iProver_top
% 2.53/1.00      | v2_struct_0(sK1) = iProver_top
% 2.53/1.00      | v2_struct_0(sK0) = iProver_top
% 2.53/1.00      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = iProver_top
% 2.53/1.00      | v1_funct_1(sK5) != iProver_top
% 2.53/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_2822]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3281,plain,
% 2.53/1.00      ( m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_1971,c_39,c_40,c_41,c_42,c_43,c_44,c_45,c_47,c_48,
% 2.53/1.00                 c_50,c_51,c_52,c_54,c_55,c_56,c_58,c_61,c_2824]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3282,plain,
% 2.53/1.00      ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top
% 2.53/1.00      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_3281]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3370,plain,
% 2.53/1.00      ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top
% 2.53/1.00      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.53/1.00      | v2_struct_0(sK1) = iProver_top
% 2.53/1.00      | v1_funct_1(sK5) != iProver_top
% 2.53/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_3355,c_3282]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3373,plain,
% 2.53/1.00      ( v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_3370,c_42,c_43,c_44,c_51,c_52,c_54,c_55,c_56,c_58]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3374,plain,
% 2.53/1.00      ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top
% 2.53/1.00      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_3373]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3379,plain,
% 2.53/1.00      ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top
% 2.53/1.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.53/1.00      | v2_struct_0(sK1) = iProver_top
% 2.53/1.00      | v1_funct_1(sK5) != iProver_top
% 2.53/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_3290,c_3374]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3432,plain,
% 2.53/1.00      ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) != iProver_top ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_3379,c_42,c_43,c_44,c_51,c_52,c_54,c_55,c_56,c_58]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3988,plain,
% 2.53/1.00      ( v5_pre_topc(sK5,sK3,sK1) != iProver_top
% 2.53/1.00      | v5_pre_topc(sK4,sK2,sK1) != iProver_top
% 2.53/1.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | r1_tsep_1(sK2,sK3) != iProver_top
% 2.53/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.53/1.00      | v2_struct_0(sK1) = iProver_top
% 2.53/1.00      | v1_funct_1(sK5) != iProver_top
% 2.53/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_3970,c_3432]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4052,plain,
% 2.53/1.00      ( v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK2,k2_tsep_1(sK0,sK2,sK3),X0_53),k3_tmap_1(sK0,X0_55,sK3,k2_tsep_1(sK0,sK2,sK3),X1_53)) = iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK0,sK3,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X1_53) != iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK0,sK2,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X0_53) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_4047,c_39,c_40,c_41,c_42,c_43,c_44,c_45,c_47,c_48,
% 2.53/1.00                 c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_3988]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4053,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK2,k2_tsep_1(sK0,sK2,sK3),X0_53),k3_tmap_1(sK0,X0_55,sK3,k2_tsep_1(sK0,sK2,sK3),X1_53)) = iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK0,sK3,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X1_53) != iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK0,sK2,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X0_53) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_55)) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_4052]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4070,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) = iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) != iProver_top
% 2.53/1.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.53/1.00      | v2_struct_0(sK1) = iProver_top
% 2.53/1.00      | v1_funct_1(sK5) != iProver_top
% 2.53/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_2039,c_4053]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_17,negated_conjecture,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
% 2.53/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_59,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_60,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2656,plain,
% 2.53/1.00      ( ~ r2_funct_2(u1_struct_0(X0_55),u1_struct_0(X1_55),k3_tmap_1(sK0,X1_55,k1_tsep_1(sK0,X0_55,sK3),X0_55,k10_tmap_1(sK0,X1_55,X0_55,sK3,X0_53,X1_53)),X0_53)
% 2.53/1.00      | r2_funct_2(u1_struct_0(k2_tsep_1(sK0,X0_55,sK3)),u1_struct_0(X1_55),k3_tmap_1(sK0,X1_55,X0_55,k2_tsep_1(sK0,X0_55,sK3),X0_53),k3_tmap_1(sK0,X1_55,sK3,k2_tsep_1(sK0,X0_55,sK3),X1_53))
% 2.53/1.00      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1_55),k3_tmap_1(sK0,X1_55,k1_tsep_1(sK0,X0_55,sK3),sK3,k10_tmap_1(sK0,X1_55,X0_55,sK3,X0_53,X1_53)),X1_53)
% 2.53/1.00      | ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 2.53/1.00      | ~ v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(X1_55))
% 2.53/1.00      | r1_tsep_1(X0_55,sK3)
% 2.53/1.00      | ~ m1_pre_topc(X0_55,sK0)
% 2.53/1.00      | ~ m1_pre_topc(sK3,sK0)
% 2.53/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 2.53/1.00      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_55))))
% 2.53/1.00      | ~ v2_pre_topc(X1_55)
% 2.53/1.00      | ~ v2_pre_topc(sK0)
% 2.53/1.00      | ~ l1_pre_topc(X1_55)
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | v2_struct_0(X0_55)
% 2.53/1.00      | v2_struct_0(X1_55)
% 2.53/1.00      | v2_struct_0(sK3)
% 2.53/1.00      | v2_struct_0(sK0)
% 2.53/1.00      | ~ v1_funct_1(X0_53)
% 2.53/1.00      | ~ v1_funct_1(X1_53) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_1259]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2985,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,sK2,k2_tsep_1(sK0,sK2,sK3),X0_53),k3_tmap_1(sK0,X0_55,sK3,k2_tsep_1(sK0,sK2,sK3),X1_53))
% 2.53/1.00      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X1_53)
% 2.53/1.00      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0_55),k3_tmap_1(sK0,X0_55,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,X0_55,sK2,sK3,X0_53,X1_53)),X0_53)
% 2.53/1.00      | ~ v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(X0_55))
% 2.53/1.00      | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_55))
% 2.53/1.00      | r1_tsep_1(sK2,sK3)
% 2.53/1.00      | ~ m1_pre_topc(sK3,sK0)
% 2.53/1.00      | ~ m1_pre_topc(sK2,sK0)
% 2.53/1.00      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_55))))
% 2.53/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_55))))
% 2.53/1.00      | ~ v2_pre_topc(X0_55)
% 2.53/1.00      | ~ v2_pre_topc(sK0)
% 2.53/1.00      | ~ l1_pre_topc(X0_55)
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | v2_struct_0(X0_55)
% 2.53/1.00      | v2_struct_0(sK3)
% 2.53/1.00      | v2_struct_0(sK2)
% 2.53/1.00      | v2_struct_0(sK0)
% 2.53/1.00      | ~ v1_funct_1(X0_53)
% 2.53/1.00      | ~ v1_funct_1(X1_53) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_2656]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3426,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),X0_53),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5))
% 2.53/1.00      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,sK5)),sK5)
% 2.53/1.00      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,sK5)),X0_53)
% 2.53/1.00      | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1))
% 2.53/1.00      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 2.53/1.00      | r1_tsep_1(sK2,sK3)
% 2.53/1.00      | ~ m1_pre_topc(sK3,sK0)
% 2.53/1.00      | ~ m1_pre_topc(sK2,sK0)
% 2.53/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.53/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.53/1.00      | ~ v2_pre_topc(sK1)
% 2.53/1.00      | ~ v2_pre_topc(sK0)
% 2.53/1.00      | ~ l1_pre_topc(sK1)
% 2.53/1.00      | ~ l1_pre_topc(sK0)
% 2.53/1.00      | v2_struct_0(sK3)
% 2.53/1.00      | v2_struct_0(sK2)
% 2.53/1.00      | v2_struct_0(sK1)
% 2.53/1.00      | v2_struct_0(sK0)
% 2.53/1.00      | ~ v1_funct_1(X0_53)
% 2.53/1.00      | ~ v1_funct_1(sK5) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_2985]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3427,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),X0_53),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) = iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,sK5)),sK5) != iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,sK5)),X0_53) != iProver_top
% 2.53/1.00      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | r1_tsep_1(sK2,sK3) = iProver_top
% 2.53/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.53/1.00      | v2_struct_0(sK3) = iProver_top
% 2.53/1.00      | v2_struct_0(sK2) = iProver_top
% 2.53/1.00      | v2_struct_0(sK1) = iProver_top
% 2.53/1.00      | v2_struct_0(sK0) = iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.53/1.00      | v1_funct_1(sK5) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3426]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3429,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) = iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) != iProver_top
% 2.53/1.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) != iProver_top
% 2.53/1.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | r1_tsep_1(sK2,sK3) = iProver_top
% 2.53/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.53/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.53/1.00      | v2_struct_0(sK3) = iProver_top
% 2.53/1.00      | v2_struct_0(sK2) = iProver_top
% 2.53/1.00      | v2_struct_0(sK1) = iProver_top
% 2.53/1.00      | v2_struct_0(sK0) = iProver_top
% 2.53/1.00      | v1_funct_1(sK5) != iProver_top
% 2.53/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_3427]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4453,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,k2_tsep_1(sK0,sK2,sK3),sK4),k3_tmap_1(sK0,sK1,sK3,k2_tsep_1(sK0,sK2,sK3),sK5)) = iProver_top ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_4070,c_39,c_40,c_41,c_42,c_43,c_44,c_45,c_47,c_48,
% 2.53/1.00                 c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,
% 2.53/1.00                 c_3429,c_3988]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_7,plain,
% 2.53/1.00      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X1,X2)),u1_struct_0(X3),k3_tmap_1(X0,X3,X1,k2_tsep_1(X0,X1,X2),X4),k3_tmap_1(X0,X3,X2,k2_tsep_1(X0,X1,X2),X5))
% 2.53/1.00      | ~ v5_pre_topc(X5,X2,X3)
% 2.53/1.00      | ~ v5_pre_topc(X4,X1,X3)
% 2.53/1.00      | v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
% 2.53/1.00      | ~ r4_tsep_1(X0,X1,X2)
% 2.53/1.00      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
% 2.53/1.00      | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
% 2.53/1.00      | r1_tsep_1(X1,X2)
% 2.53/1.00      | ~ m1_pre_topc(X2,X0)
% 2.53/1.00      | ~ m1_pre_topc(X1,X0)
% 2.53/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
% 2.53/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.53/1.00      | ~ v2_pre_topc(X3)
% 2.53/1.00      | ~ v2_pre_topc(X0)
% 2.53/1.00      | ~ l1_pre_topc(X3)
% 2.53/1.00      | ~ l1_pre_topc(X0)
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | v2_struct_0(X3)
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | ~ v1_funct_1(X5)
% 2.53/1.00      | ~ v1_funct_1(X4) ),
% 2.53/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1257,plain,
% 2.53/1.00      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0_55,X1_55,X2_55)),u1_struct_0(X3_55),k3_tmap_1(X0_55,X3_55,X1_55,k2_tsep_1(X0_55,X1_55,X2_55),X0_53),k3_tmap_1(X0_55,X3_55,X2_55,k2_tsep_1(X0_55,X1_55,X2_55),X1_53))
% 2.53/1.00      | ~ v5_pre_topc(X1_53,X2_55,X3_55)
% 2.53/1.00      | ~ v5_pre_topc(X0_53,X1_55,X3_55)
% 2.53/1.00      | v5_pre_topc(k10_tmap_1(X0_55,X3_55,X1_55,X2_55,X0_53,X1_53),k1_tsep_1(X0_55,X1_55,X2_55),X3_55)
% 2.53/1.00      | ~ r4_tsep_1(X0_55,X1_55,X2_55)
% 2.53/1.00      | ~ v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X3_55))
% 2.53/1.00      | ~ v1_funct_2(X0_53,u1_struct_0(X1_55),u1_struct_0(X3_55))
% 2.53/1.00      | r1_tsep_1(X1_55,X2_55)
% 2.53/1.00      | ~ m1_pre_topc(X2_55,X0_55)
% 2.53/1.00      | ~ m1_pre_topc(X1_55,X0_55)
% 2.53/1.00      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X3_55))))
% 2.53/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X3_55))))
% 2.53/1.00      | ~ v2_pre_topc(X3_55)
% 2.53/1.00      | ~ v2_pre_topc(X0_55)
% 2.53/1.00      | ~ l1_pre_topc(X3_55)
% 2.53/1.00      | ~ l1_pre_topc(X0_55)
% 2.53/1.00      | v2_struct_0(X1_55)
% 2.53/1.00      | v2_struct_0(X2_55)
% 2.53/1.00      | v2_struct_0(X0_55)
% 2.53/1.00      | v2_struct_0(X3_55)
% 2.53/1.00      | ~ v1_funct_1(X0_53)
% 2.53/1.00      | ~ v1_funct_1(X1_53) ),
% 2.53/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1966,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(k2_tsep_1(X0_55,X1_55,X2_55)),u1_struct_0(X3_55),k3_tmap_1(X0_55,X3_55,X1_55,k2_tsep_1(X0_55,X1_55,X2_55),X0_53),k3_tmap_1(X0_55,X3_55,X2_55,k2_tsep_1(X0_55,X1_55,X2_55),X1_53)) != iProver_top
% 2.53/1.00      | v5_pre_topc(X1_53,X2_55,X3_55) != iProver_top
% 2.53/1.00      | v5_pre_topc(X0_53,X1_55,X3_55) != iProver_top
% 2.53/1.00      | v5_pre_topc(k10_tmap_1(X0_55,X3_55,X1_55,X2_55,X0_53,X1_53),k1_tsep_1(X0_55,X1_55,X2_55),X3_55) = iProver_top
% 2.53/1.00      | r4_tsep_1(X0_55,X1_55,X2_55) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X3_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X0_53,u1_struct_0(X1_55),u1_struct_0(X3_55)) != iProver_top
% 2.53/1.00      | r1_tsep_1(X1_55,X2_55) = iProver_top
% 2.53/1.00      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 2.53/1.00      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X3_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X3_55)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | v2_pre_topc(X3_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X3_55) != iProver_top
% 2.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X2_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X1_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X3_55) = iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1257]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2311,plain,
% 2.53/1.00      ( r2_funct_2(u1_struct_0(k2_tsep_1(X0_55,X1_55,X2_55)),u1_struct_0(X3_55),k3_tmap_1(X0_55,X3_55,X1_55,k2_tsep_1(X0_55,X1_55,X2_55),X0_53),k3_tmap_1(X0_55,X3_55,X2_55,k2_tsep_1(X0_55,X1_55,X2_55),X1_53)) != iProver_top
% 2.53/1.00      | v5_pre_topc(X1_53,X2_55,X3_55) != iProver_top
% 2.53/1.00      | v5_pre_topc(X0_53,X1_55,X3_55) != iProver_top
% 2.53/1.00      | v5_pre_topc(k10_tmap_1(X0_55,X3_55,X1_55,X2_55,X0_53,X1_53),k1_tsep_1(X0_55,X1_55,X2_55),X3_55) = iProver_top
% 2.53/1.00      | r4_tsep_1(X0_55,X1_55,X2_55) != iProver_top
% 2.53/1.00      | v1_funct_2(X1_53,u1_struct_0(X2_55),u1_struct_0(X3_55)) != iProver_top
% 2.53/1.00      | v1_funct_2(X0_53,u1_struct_0(X1_55),u1_struct_0(X3_55)) != iProver_top
% 2.53/1.00      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 2.53/1.00      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.53/1.00      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X3_55)))) != iProver_top
% 2.53/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X3_55)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | v2_pre_topc(X3_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.53/1.00      | l1_pre_topc(X3_55) != iProver_top
% 2.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X2_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X1_55) = iProver_top
% 2.53/1.00      | v2_struct_0(X3_55) = iProver_top
% 2.53/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.53/1.00      | v1_funct_1(X1_53) != iProver_top ),
% 2.53/1.00      inference(forward_subsumption_resolution,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_1966,c_1969]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4621,plain,
% 2.53/1.00      ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) = iProver_top
% 2.53/1.00      | v5_pre_topc(sK5,sK3,sK1) != iProver_top
% 2.53/1.00      | v5_pre_topc(sK4,sK2,sK1) != iProver_top
% 2.53/1.00      | r4_tsep_1(sK0,sK2,sK3) != iProver_top
% 2.53/1.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.53/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.53/1.00      | v2_struct_0(sK3) = iProver_top
% 2.53/1.00      | v2_struct_0(sK2) = iProver_top
% 2.53/1.00      | v2_struct_0(sK1) = iProver_top
% 2.53/1.00      | v2_struct_0(sK0) = iProver_top
% 2.53/1.00      | v1_funct_1(sK5) != iProver_top
% 2.53/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_4453,c_2311]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4622,plain,
% 2.53/1.00      ( v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) = iProver_top
% 2.53/1.00      | v5_pre_topc(sK5,sK3,sK1) != iProver_top
% 2.53/1.00      | v5_pre_topc(sK4,sK2,sK1) != iProver_top
% 2.53/1.00      | r4_tsep_1(sK0,sK2,sK3) != iProver_top
% 2.53/1.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.53/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.53/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.53/1.00      | v2_struct_0(sK3) = iProver_top
% 2.53/1.00      | v2_struct_0(sK2) = iProver_top
% 2.53/1.00      | v2_struct_0(sK1) = iProver_top
% 2.53/1.00      | v2_struct_0(sK0) = iProver_top
% 2.53/1.00      | v1_funct_1(sK5) != iProver_top
% 2.53/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_4621,c_1249]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(contradiction,plain,
% 2.53/1.01      ( $false ),
% 2.53/1.01      inference(minisat,
% 2.53/1.01                [status(thm)],
% 2.53/1.01                [c_4622,c_3379,c_2682,c_58,c_57,c_56,c_55,c_54,c_53,c_52,
% 2.53/1.01                 c_51,c_50,c_49,c_48,c_47,c_46,c_45,c_44,c_43,c_42,c_41,
% 2.53/1.01                 c_40,c_39]) ).
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.53/1.01  
% 2.53/1.01  ------                               Statistics
% 2.53/1.01  
% 2.53/1.01  ------ General
% 2.53/1.01  
% 2.53/1.01  abstr_ref_over_cycles:                  0
% 2.53/1.01  abstr_ref_under_cycles:                 0
% 2.53/1.01  gc_basic_clause_elim:                   0
% 2.53/1.01  forced_gc_time:                         0
% 2.53/1.01  parsing_time:                           0.014
% 2.53/1.01  unif_index_cands_time:                  0.
% 2.53/1.01  unif_index_add_time:                    0.
% 2.53/1.01  orderings_time:                         0.
% 2.53/1.01  out_proof_time:                         0.02
% 2.53/1.01  total_time:                             0.267
% 2.53/1.01  num_of_symbols:                         58
% 2.53/1.01  num_of_terms:                           4567
% 2.53/1.01  
% 2.53/1.01  ------ Preprocessing
% 2.53/1.01  
% 2.53/1.01  num_of_splits:                          0
% 2.53/1.01  num_of_split_atoms:                     0
% 2.53/1.01  num_of_reused_defs:                     0
% 2.53/1.01  num_eq_ax_congr_red:                    16
% 2.53/1.01  num_of_sem_filtered_clauses:            1
% 2.53/1.01  num_of_subtypes:                        5
% 2.53/1.01  monotx_restored_types:                  0
% 2.53/1.01  sat_num_of_epr_types:                   0
% 2.53/1.01  sat_num_of_non_cyclic_types:            0
% 2.53/1.01  sat_guarded_non_collapsed_types:        0
% 2.53/1.01  num_pure_diseq_elim:                    0
% 2.53/1.01  simp_replaced_by:                       0
% 2.53/1.01  res_preprocessed:                       156
% 2.53/1.01  prep_upred:                             0
% 2.53/1.01  prep_unflattend:                        17
% 2.53/1.01  smt_new_axioms:                         0
% 2.53/1.01  pred_elim_cands:                        12
% 2.53/1.01  pred_elim:                              0
% 2.53/1.01  pred_elim_cl:                           0
% 2.53/1.01  pred_elim_cycles:                       2
% 2.53/1.01  merged_defs:                            0
% 2.53/1.01  merged_defs_ncl:                        0
% 2.53/1.01  bin_hyper_res:                          0
% 2.53/1.01  prep_cycles:                            3
% 2.53/1.01  pred_elim_time:                         0.036
% 2.53/1.01  splitting_time:                         0.
% 2.53/1.01  sem_filter_time:                        0.
% 2.53/1.01  monotx_time:                            0.
% 2.53/1.01  subtype_inf_time:                       0.002
% 2.53/1.01  
% 2.53/1.01  ------ Problem properties
% 2.53/1.01  
% 2.53/1.01  clauses:                                39
% 2.53/1.01  conjectures:                            24
% 2.53/1.01  epr:                                    17
% 2.53/1.01  horn:                                   24
% 2.53/1.01  ground:                                 24
% 2.53/1.01  unary:                                  23
% 2.53/1.01  binary:                                 0
% 2.53/1.01  lits:                                   304
% 2.53/1.01  lits_eq:                                1
% 2.53/1.01  fd_pure:                                0
% 2.53/1.01  fd_pseudo:                              0
% 2.53/1.01  fd_cond:                                0
% 2.53/1.01  fd_pseudo_cond:                         0
% 2.53/1.01  ac_symbols:                             0
% 2.53/1.01  
% 2.53/1.01  ------ Propositional Solver
% 2.53/1.01  
% 2.53/1.01  prop_solver_calls:                      22
% 2.53/1.01  prop_fast_solver_calls:                 2901
% 2.53/1.01  smt_solver_calls:                       0
% 2.53/1.01  smt_fast_solver_calls:                  0
% 2.53/1.01  prop_num_of_clauses:                    1167
% 2.53/1.01  prop_preprocess_simplified:             4799
% 2.53/1.01  prop_fo_subsumed:                       110
% 2.53/1.01  prop_solver_time:                       0.
% 2.53/1.01  smt_solver_time:                        0.
% 2.53/1.01  smt_fast_solver_time:                   0.
% 2.53/1.01  prop_fast_solver_time:                  0.
% 2.53/1.01  prop_unsat_core_time:                   0.
% 2.53/1.01  
% 2.53/1.01  ------ QBF
% 2.53/1.01  
% 2.53/1.01  qbf_q_res:                              0
% 2.53/1.01  qbf_num_tautologies:                    0
% 2.53/1.01  qbf_prep_cycles:                        0
% 2.53/1.01  
% 2.53/1.01  ------ BMC1
% 2.53/1.01  
% 2.53/1.01  bmc1_current_bound:                     -1
% 2.53/1.01  bmc1_last_solved_bound:                 -1
% 2.53/1.01  bmc1_unsat_core_size:                   -1
% 2.53/1.01  bmc1_unsat_core_parents_size:           -1
% 2.53/1.01  bmc1_merge_next_fun:                    0
% 2.53/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.53/1.01  
% 2.53/1.01  ------ Instantiation
% 2.53/1.01  
% 2.53/1.01  inst_num_of_clauses:                    322
% 2.53/1.01  inst_num_in_passive:                    3
% 2.53/1.01  inst_num_in_active:                     237
% 2.53/1.01  inst_num_in_unprocessed:                82
% 2.53/1.01  inst_num_of_loops:                      240
% 2.53/1.01  inst_num_of_learning_restarts:          0
% 2.53/1.01  inst_num_moves_active_passive:          1
% 2.53/1.01  inst_lit_activity:                      0
% 2.53/1.01  inst_lit_activity_moves:                0
% 2.53/1.01  inst_num_tautologies:                   0
% 2.53/1.01  inst_num_prop_implied:                  0
% 2.53/1.01  inst_num_existing_simplified:           0
% 2.53/1.01  inst_num_eq_res_simplified:             0
% 2.53/1.01  inst_num_child_elim:                    0
% 2.53/1.01  inst_num_of_dismatching_blockings:      0
% 2.53/1.01  inst_num_of_non_proper_insts:           243
% 2.53/1.01  inst_num_of_duplicates:                 0
% 2.53/1.01  inst_inst_num_from_inst_to_res:         0
% 2.53/1.01  inst_dismatching_checking_time:         0.
% 2.53/1.01  
% 2.53/1.01  ------ Resolution
% 2.53/1.01  
% 2.53/1.01  res_num_of_clauses:                     0
% 2.53/1.01  res_num_in_passive:                     0
% 2.53/1.01  res_num_in_active:                      0
% 2.53/1.01  res_num_of_loops:                       159
% 2.53/1.01  res_forward_subset_subsumed:            11
% 2.53/1.01  res_backward_subset_subsumed:           0
% 2.53/1.01  res_forward_subsumed:                   0
% 2.53/1.01  res_backward_subsumed:                  0
% 2.53/1.01  res_forward_subsumption_resolution:     0
% 2.53/1.01  res_backward_subsumption_resolution:    0
% 2.53/1.01  res_clause_to_clause_subsumption:       202
% 2.53/1.01  res_orphan_elimination:                 0
% 2.53/1.01  res_tautology_del:                      10
% 2.53/1.01  res_num_eq_res_simplified:              0
% 2.53/1.01  res_num_sel_changes:                    0
% 2.53/1.01  res_moves_from_active_to_pass:          0
% 2.53/1.01  
% 2.53/1.01  ------ Superposition
% 2.53/1.01  
% 2.53/1.01  sup_time_total:                         0.
% 2.53/1.01  sup_time_generating:                    0.
% 2.53/1.01  sup_time_sim_full:                      0.
% 2.53/1.01  sup_time_sim_immed:                     0.
% 2.53/1.01  
% 2.53/1.01  sup_num_of_clauses:                     52
% 2.53/1.01  sup_num_in_active:                      46
% 2.53/1.01  sup_num_in_passive:                     6
% 2.53/1.01  sup_num_of_loops:                       47
% 2.53/1.01  sup_fw_superposition:                   19
% 2.53/1.01  sup_bw_superposition:                   4
% 2.53/1.01  sup_immediate_simplified:               5
% 2.53/1.01  sup_given_eliminated:                   0
% 2.53/1.01  comparisons_done:                       0
% 2.53/1.01  comparisons_avoided:                    0
% 2.53/1.01  
% 2.53/1.01  ------ Simplifications
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  sim_fw_subset_subsumed:                 0
% 2.53/1.01  sim_bw_subset_subsumed:                 2
% 2.53/1.01  sim_fw_subsumed:                        5
% 2.53/1.01  sim_bw_subsumed:                        0
% 2.53/1.01  sim_fw_subsumption_res:                 2
% 2.53/1.01  sim_bw_subsumption_res:                 0
% 2.53/1.01  sim_tautology_del:                      0
% 2.53/1.01  sim_eq_tautology_del:                   0
% 2.53/1.01  sim_eq_res_simp:                        0
% 2.53/1.01  sim_fw_demodulated:                     0
% 2.53/1.01  sim_bw_demodulated:                     0
% 2.53/1.01  sim_light_normalised:                   6
% 2.53/1.01  sim_joinable_taut:                      0
% 2.53/1.01  sim_joinable_simp:                      0
% 2.53/1.01  sim_ac_normalised:                      0
% 2.53/1.01  sim_smt_subsumption:                    0
% 2.53/1.01  
%------------------------------------------------------------------------------
