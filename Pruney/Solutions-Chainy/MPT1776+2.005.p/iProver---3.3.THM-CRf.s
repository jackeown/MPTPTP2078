%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:21 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  229 (1725 expanded)
%              Number of clauses        :  144 ( 344 expanded)
%              Number of leaves         :   22 ( 712 expanded)
%              Depth                    :   28
%              Number of atoms          : 1731 (32475 expanded)
%              Number of equality atoms :  401 (2423 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal clause size      :   46 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X2,X1)
                          & v1_tsep_1(X2,X1) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X0,X4,X5)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & m1_pre_topc(X2,X1)
                            & v1_tsep_1(X2,X1) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X0,X4,X5)
                                    <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
            | ~ r1_tmap_1(X3,X0,X4,X5) )
          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
            | r1_tmap_1(X3,X0,X4,X5) )
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7)
          | ~ r1_tmap_1(X3,X0,X4,X5) )
        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7)
          | r1_tmap_1(X3,X0,X4,X5) )
        & sK7 = X5
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                | ~ r1_tmap_1(X3,X0,X4,X5) )
              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                | r1_tmap_1(X3,X0,X4,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
              | ~ r1_tmap_1(X3,X0,X4,sK6) )
            & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
              | r1_tmap_1(X3,X0,X4,sK6) )
            & sK6 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                    | ~ r1_tmap_1(X3,X0,X4,X5) )
                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                    | r1_tmap_1(X3,X0,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_pre_topc(X2,X3)
          & m1_pre_topc(X2,X1)
          & v1_tsep_1(X2,X1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X6)
                  | ~ r1_tmap_1(X3,X0,sK5,X5) )
                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X6)
                  | r1_tmap_1(X3,X0,sK5,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & m1_pre_topc(X2,X1)
        & v1_tsep_1(X2,X1)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                        | ~ r1_tmap_1(X3,X0,X4,X5) )
                      & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                        | r1_tmap_1(X3,X0,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(X2,X1)
              & v1_tsep_1(X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X1)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X6)
                      | ~ r1_tmap_1(sK4,X0,X4,X5) )
                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X6)
                      | r1_tmap_1(sK4,X0,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK4)) )
            & m1_pre_topc(X2,sK4)
            & m1_pre_topc(X2,X1)
            & v1_tsep_1(X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X1)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,X0,X4,X5) )
                          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                            | r1_tmap_1(X3,X0,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X2,X1)
                  & v1_tsep_1(X2,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X6)
                          | ~ r1_tmap_1(X3,X0,X4,X5) )
                        & ( r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X6)
                          | r1_tmap_1(X3,X0,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK3)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK3,X3)
                & m1_pre_topc(sK3,X1)
                & v1_tsep_1(sK3,X1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,X0,X4,X5) )
                            & ( r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X6)
                              | r1_tmap_1(X3,X0,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X2,sK2)
                    & v1_tsep_1(X2,sK2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X0,X4,X5) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X0,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & m1_pre_topc(X2,X1)
                        & v1_tsep_1(X2,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X1)
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
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,sK1,X4,X5) )
                              & ( r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,sK1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
      | ~ r1_tmap_1(sK4,sK1,sK5,sK6) )
    & ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
      | r1_tmap_1(sK4,sK1,sK5,sK6) )
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK3))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK3,sK2)
    & v1_tsep_1(sK3,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f42,f49,f48,f47,f46,f45,f44,f43])).

fof(f81,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f71,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f86,plain,
    ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
    | ~ r1_tmap_1(sK4,sK1,sK5,sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f50])).

fof(f72,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_tmap_1(X1,X0,X2,X4)
                              | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) ) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
    | r1_tmap_1(sK4,sK1,sK5,sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X4)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f79,plain,(
    v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1316,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2068,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1316])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1312,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2072,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1312])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1330,plain,
    ( r2_hidden(sK0(X0_54,X1_54),X0_54)
    | r1_tarski(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2055,plain,
    ( r2_hidden(sK0(X0_54,X1_54),X0_54) = iProver_top
    | r1_tarski(X0_54,X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1330])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1323,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ l1_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2062,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53))) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1323])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1329,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ r2_hidden(X0_55,X0_54)
    | r2_hidden(X0_55,X1_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2056,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
    | r2_hidden(X0_55,X0_54) != iProver_top
    | r2_hidden(X0_55,X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1329])).

cnf(c_2978,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | r2_hidden(X0_55,u1_struct_0(X0_53)) != iProver_top
    | r2_hidden(X0_55,u1_struct_0(X1_53)) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2062,c_2056])).

cnf(c_3753,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | r2_hidden(sK0(u1_struct_0(X0_53),X0_54),u1_struct_0(X1_53)) = iProver_top
    | r1_tarski(u1_struct_0(X0_53),X0_54) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2055,c_2978])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1331,plain,
    ( ~ r2_hidden(sK0(X0_54,X1_54),X1_54)
    | r1_tarski(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2054,plain,
    ( r2_hidden(sK0(X0_54,X1_54),X1_54) != iProver_top
    | r1_tarski(X0_54,X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1331])).

cnf(c_3828,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53)) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_3753,c_2054])).

cnf(c_9,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1324,plain,
    ( ~ v1_tsep_1(X0_53,X1_53)
    | v1_tsep_1(X0_53,X2_53)
    | ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_pre_topc(X2_53,X1_53)
    | ~ r1_tarski(u1_struct_0(X0_53),u1_struct_0(X2_53))
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2061,plain,
    ( v1_tsep_1(X0_53,X1_53) != iProver_top
    | v1_tsep_1(X0_53,X2_53) = iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X2_53,X1_53) != iProver_top
    | r1_tarski(u1_struct_0(X0_53),u1_struct_0(X2_53)) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1324])).

cnf(c_4259,plain,
    ( v1_tsep_1(X0_53,X1_53) != iProver_top
    | v1_tsep_1(X0_53,X2_53) = iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X2_53,X1_53) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_3828,c_2061])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1327,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2058,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1327])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1322,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_pre_topc(X2_53,X0_53)
    | m1_pre_topc(X2_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2063,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X2_53,X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1322])).

cnf(c_4870,plain,
    ( v1_tsep_1(X0_53,X1_53) != iProver_top
    | v1_tsep_1(X0_53,X2_53) = iProver_top
    | m1_pre_topc(X2_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4259,c_2058,c_2063])).

cnf(c_4874,plain,
    ( v1_tsep_1(X0_53,sK4) = iProver_top
    | v1_tsep_1(X0_53,sK2) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2072,c_4870])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_39,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_40,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_41,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_44,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5097,plain,
    ( v1_tsep_1(X0_53,sK4) = iProver_top
    | v1_tsep_1(X0_53,sK2) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4874,c_39,c_40,c_41,c_44])).

cnf(c_5106,plain,
    ( v1_tsep_1(sK3,sK4) = iProver_top
    | v1_tsep_1(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2068,c_5097])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_759,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X4) != u1_struct_0(sK1)
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_760,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_759])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_764,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_760,c_25])).

cnf(c_765,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_764])).

cnf(c_796,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_765,c_14])).

cnf(c_1301,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_pre_topc(X1_53,X2_53)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X3_53))))
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | ~ l1_pre_topc(X2_53)
    | ~ l1_pre_topc(X3_53)
    | ~ v2_pre_topc(X2_53)
    | ~ v2_pre_topc(X3_53)
    | k2_partfun1(u1_struct_0(X1_53),u1_struct_0(X3_53),sK5,u1_struct_0(X0_53)) = k3_tmap_1(X2_53,X3_53,X1_53,X0_53,sK5)
    | u1_struct_0(X1_53) != u1_struct_0(sK4)
    | u1_struct_0(X3_53) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_796])).

cnf(c_2083,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK5,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK5)
    | u1_struct_0(X0_53) != u1_struct_0(sK4)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1301])).

cnf(c_4000,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK5,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK5)
    | u1_struct_0(X0_53) != u1_struct_0(sK4)
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2083])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_36,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_37,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_38,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4152,plain,
    ( v2_pre_topc(X2_53) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | u1_struct_0(X0_53) != u1_struct_0(sK4)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK5,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK5)
    | l1_pre_topc(X2_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4000,c_36,c_37,c_38])).

cnf(c_4153,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK5,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK5)
    | u1_struct_0(X0_53) != u1_struct_0(sK4)
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4152])).

cnf(c_4164,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK4,X0_53,sK5)
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_53) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4153])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4424,plain,
    ( m1_pre_topc(sK4,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK4,X0_53,sK5)
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4164,c_48])).

cnf(c_4425,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK4,X0_53,sK5)
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4424])).

cnf(c_4436,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(X0_53,sK1,sK4,sK3,sK5)
    | m1_pre_topc(sK4,X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2068,c_4425])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_810,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_24])).

cnf(c_811,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_815,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_811,c_25])).

cnf(c_816,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_815])).

cnf(c_1300,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X2_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | k2_partfun1(u1_struct_0(X1_53),u1_struct_0(X2_53),sK5,u1_struct_0(X0_53)) = k2_tmap_1(X1_53,X2_53,sK5,X0_53)
    | u1_struct_0(X1_53) != u1_struct_0(sK4)
    | u1_struct_0(X2_53) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_816])).

cnf(c_2084,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK5,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,sK5,X2_53)
    | u1_struct_0(X0_53) != u1_struct_0(sK4)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1300])).

cnf(c_3120,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK5,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK5,X1_53)
    | u1_struct_0(X0_53) != u1_struct_0(sK4)
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2084])).

cnf(c_3912,plain,
    ( v2_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | u1_struct_0(X0_53) != u1_struct_0(sK4)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK5,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK5,X1_53)
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3120,c_36,c_37,c_38])).

cnf(c_3913,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK5,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK5,X1_53)
    | u1_struct_0(X0_53) != u1_struct_0(sK4)
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_3912])).

cnf(c_3923,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_53)) = k2_tmap_1(sK4,sK1,sK5,X0_53)
    | m1_pre_topc(X0_53,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3913])).

cnf(c_45,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2573,plain,
    ( ~ m1_pre_topc(sK4,X0_53)
    | ~ l1_pre_topc(X0_53)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_2690,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2573])).

cnf(c_2691,plain,
    ( m1_pre_topc(sK4,sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2690])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1328,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53)
    | v2_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2057,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1328])).

cnf(c_2829,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2072,c_2057])).

cnf(c_4086,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_53)) = k2_tmap_1(sK4,sK1,sK5,X0_53)
    | m1_pre_topc(X0_53,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3923,c_40,c_41,c_44,c_45,c_48,c_2691,c_2829])).

cnf(c_4094,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_2068,c_4086])).

cnf(c_4437,plain,
    ( k3_tmap_1(X0_53,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
    | m1_pre_topc(sK4,X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4436,c_4094])).

cnf(c_4447,plain,
    ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2072,c_4437])).

cnf(c_4508,plain,
    ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4447,c_39,c_40,c_41])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK6)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1321,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK6)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2064,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK6) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1321])).

cnf(c_17,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1319,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2149,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2064,c_1319])).

cnf(c_4512,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4508,c_2149])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_42,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_51,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_53,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1333,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_2397,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1333])).

cnf(c_3548,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1333])).

cnf(c_13,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_11,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_179,plain,
    ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_11])).

cnf(c_180,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_593,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_180,c_24])).

cnf(c_594,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_598,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_594,c_25])).

cnf(c_599,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_598])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_634,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_599,c_5])).

cnf(c_1303,plain,
    ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,sK5,X0_53),X0_54)
    | ~ r1_tmap_1(X2_53,X1_53,sK5,X0_54)
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X2_53) != u1_struct_0(sK4)
    | u1_struct_0(X1_53) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_634])).

cnf(c_2662,plain,
    ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK4,X1_53,sK5,X0_53),X0_54)
    | ~ r1_tmap_1(sK4,X1_53,sK5,X0_54)
    | ~ m1_pre_topc(X0_53,sK4)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1303])).

cnf(c_3479,plain,
    ( ~ r1_tmap_1(sK4,X0_53,sK5,X0_54)
    | r1_tmap_1(sK3,X0_53,k2_tmap_1(sK4,X0_53,sK5,sK3),X0_54)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2662])).

cnf(c_4095,plain,
    ( ~ r1_tmap_1(sK4,X0_53,sK5,sK7)
    | r1_tmap_1(sK3,X0_53,k2_tmap_1(sK4,X0_53,sK5,sK3),sK7)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3479])).

cnf(c_4096,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(sK4,X0_53,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,X0_53,k2_tmap_1(sK4,X0_53,sK5,sK3),sK7) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4095])).

cnf(c_4098,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4096])).

cnf(c_4524,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4512,c_36,c_37,c_38,c_40,c_41,c_42,c_44,c_45,c_48,c_51,c_53,c_2397,c_2691,c_2829,c_3548,c_4098])).

cnf(c_16,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK6)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1320,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK6)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2065,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK6) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1320])).

cnf(c_2138,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2065,c_1319])).

cnf(c_4511,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4508,c_2138])).

cnf(c_12,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_650,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_651,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_655,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ v1_tsep_1(X0,X2)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_651,c_25])).

cnf(c_656,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_655])).

cnf(c_693,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_656,c_5])).

cnf(c_1302,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,sK5,X0_53),X0_54)
    | r1_tmap_1(X2_53,X1_53,sK5,X0_54)
    | ~ v1_tsep_1(X0_53,X2_53)
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X2_53) != u1_struct_0(sK4)
    | u1_struct_0(X1_53) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_693])).

cnf(c_2661,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK4,X1_53,sK5,X0_53),X0_54)
    | r1_tmap_1(sK4,X1_53,sK5,X0_54)
    | ~ v1_tsep_1(X0_53,sK4)
    | ~ m1_pre_topc(X0_53,sK4)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1302])).

cnf(c_3484,plain,
    ( r1_tmap_1(sK4,X0_53,sK5,X0_54)
    | ~ r1_tmap_1(sK3,X0_53,k2_tmap_1(sK4,X0_53,sK5,sK3),X0_54)
    | ~ v1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2661])).

cnf(c_3713,plain,
    ( r1_tmap_1(sK4,X0_53,sK5,sK7)
    | ~ r1_tmap_1(sK3,X0_53,k2_tmap_1(sK4,X0_53,sK5,sK3),sK7)
    | ~ v1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3484])).

cnf(c_3714,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(sK4,X0_53,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,X0_53,k2_tmap_1(sK4,X0_53,sK5,sK3),sK7) != iProver_top
    | v1_tsep_1(sK3,sK4) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3713])).

cnf(c_3716,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) != iProver_top
    | v1_tsep_1(sK3,sK4) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3714])).

cnf(c_22,negated_conjecture,
    ( v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_49,plain,
    ( v1_tsep_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5106,c_4524,c_4511,c_3716,c_3548,c_2829,c_2691,c_2397,c_53,c_51,c_49,c_48,c_45,c_44,c_42,c_41,c_40,c_38,c_37,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.38/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.01  
% 2.38/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.38/1.01  
% 2.38/1.01  ------  iProver source info
% 2.38/1.01  
% 2.38/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.38/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.38/1.01  git: non_committed_changes: false
% 2.38/1.01  git: last_make_outside_of_git: false
% 2.38/1.01  
% 2.38/1.01  ------ 
% 2.38/1.01  
% 2.38/1.01  ------ Input Options
% 2.38/1.01  
% 2.38/1.01  --out_options                           all
% 2.38/1.01  --tptp_safe_out                         true
% 2.38/1.01  --problem_path                          ""
% 2.38/1.01  --include_path                          ""
% 2.38/1.01  --clausifier                            res/vclausify_rel
% 2.38/1.01  --clausifier_options                    --mode clausify
% 2.38/1.01  --stdin                                 false
% 2.38/1.01  --stats_out                             all
% 2.38/1.01  
% 2.38/1.01  ------ General Options
% 2.38/1.01  
% 2.38/1.01  --fof                                   false
% 2.38/1.01  --time_out_real                         305.
% 2.38/1.01  --time_out_virtual                      -1.
% 2.38/1.01  --symbol_type_check                     false
% 2.38/1.01  --clausify_out                          false
% 2.38/1.01  --sig_cnt_out                           false
% 2.38/1.01  --trig_cnt_out                          false
% 2.38/1.01  --trig_cnt_out_tolerance                1.
% 2.38/1.01  --trig_cnt_out_sk_spl                   false
% 2.38/1.01  --abstr_cl_out                          false
% 2.38/1.01  
% 2.38/1.01  ------ Global Options
% 2.38/1.01  
% 2.38/1.01  --schedule                              default
% 2.38/1.01  --add_important_lit                     false
% 2.38/1.01  --prop_solver_per_cl                    1000
% 2.38/1.01  --min_unsat_core                        false
% 2.38/1.01  --soft_assumptions                      false
% 2.38/1.01  --soft_lemma_size                       3
% 2.38/1.01  --prop_impl_unit_size                   0
% 2.38/1.01  --prop_impl_unit                        []
% 2.38/1.01  --share_sel_clauses                     true
% 2.38/1.01  --reset_solvers                         false
% 2.38/1.01  --bc_imp_inh                            [conj_cone]
% 2.38/1.01  --conj_cone_tolerance                   3.
% 2.38/1.01  --extra_neg_conj                        none
% 2.38/1.01  --large_theory_mode                     true
% 2.38/1.01  --prolific_symb_bound                   200
% 2.38/1.01  --lt_threshold                          2000
% 2.38/1.01  --clause_weak_htbl                      true
% 2.38/1.01  --gc_record_bc_elim                     false
% 2.38/1.01  
% 2.38/1.01  ------ Preprocessing Options
% 2.38/1.01  
% 2.38/1.01  --preprocessing_flag                    true
% 2.38/1.01  --time_out_prep_mult                    0.1
% 2.38/1.01  --splitting_mode                        input
% 2.38/1.01  --splitting_grd                         true
% 2.38/1.01  --splitting_cvd                         false
% 2.38/1.01  --splitting_cvd_svl                     false
% 2.38/1.01  --splitting_nvd                         32
% 2.38/1.01  --sub_typing                            true
% 2.38/1.01  --prep_gs_sim                           true
% 2.38/1.01  --prep_unflatten                        true
% 2.38/1.01  --prep_res_sim                          true
% 2.38/1.01  --prep_upred                            true
% 2.38/1.01  --prep_sem_filter                       exhaustive
% 2.38/1.01  --prep_sem_filter_out                   false
% 2.38/1.01  --pred_elim                             true
% 2.38/1.01  --res_sim_input                         true
% 2.38/1.01  --eq_ax_congr_red                       true
% 2.38/1.01  --pure_diseq_elim                       true
% 2.38/1.01  --brand_transform                       false
% 2.38/1.01  --non_eq_to_eq                          false
% 2.38/1.01  --prep_def_merge                        true
% 2.38/1.01  --prep_def_merge_prop_impl              false
% 2.38/1.01  --prep_def_merge_mbd                    true
% 2.38/1.01  --prep_def_merge_tr_red                 false
% 2.38/1.01  --prep_def_merge_tr_cl                  false
% 2.38/1.01  --smt_preprocessing                     true
% 2.38/1.01  --smt_ac_axioms                         fast
% 2.38/1.01  --preprocessed_out                      false
% 2.38/1.01  --preprocessed_stats                    false
% 2.38/1.01  
% 2.38/1.01  ------ Abstraction refinement Options
% 2.38/1.01  
% 2.38/1.01  --abstr_ref                             []
% 2.38/1.01  --abstr_ref_prep                        false
% 2.38/1.01  --abstr_ref_until_sat                   false
% 2.38/1.01  --abstr_ref_sig_restrict                funpre
% 2.38/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.38/1.01  --abstr_ref_under                       []
% 2.38/1.01  
% 2.38/1.01  ------ SAT Options
% 2.38/1.01  
% 2.38/1.01  --sat_mode                              false
% 2.38/1.01  --sat_fm_restart_options                ""
% 2.38/1.01  --sat_gr_def                            false
% 2.38/1.01  --sat_epr_types                         true
% 2.38/1.01  --sat_non_cyclic_types                  false
% 2.38/1.01  --sat_finite_models                     false
% 2.38/1.01  --sat_fm_lemmas                         false
% 2.38/1.01  --sat_fm_prep                           false
% 2.38/1.01  --sat_fm_uc_incr                        true
% 2.38/1.01  --sat_out_model                         small
% 2.38/1.01  --sat_out_clauses                       false
% 2.38/1.01  
% 2.38/1.01  ------ QBF Options
% 2.38/1.01  
% 2.38/1.01  --qbf_mode                              false
% 2.38/1.01  --qbf_elim_univ                         false
% 2.38/1.01  --qbf_dom_inst                          none
% 2.38/1.01  --qbf_dom_pre_inst                      false
% 2.38/1.01  --qbf_sk_in                             false
% 2.38/1.01  --qbf_pred_elim                         true
% 2.38/1.01  --qbf_split                             512
% 2.38/1.01  
% 2.38/1.01  ------ BMC1 Options
% 2.38/1.01  
% 2.38/1.01  --bmc1_incremental                      false
% 2.38/1.01  --bmc1_axioms                           reachable_all
% 2.38/1.01  --bmc1_min_bound                        0
% 2.38/1.01  --bmc1_max_bound                        -1
% 2.38/1.01  --bmc1_max_bound_default                -1
% 2.38/1.01  --bmc1_symbol_reachability              true
% 2.38/1.01  --bmc1_property_lemmas                  false
% 2.38/1.01  --bmc1_k_induction                      false
% 2.38/1.01  --bmc1_non_equiv_states                 false
% 2.38/1.01  --bmc1_deadlock                         false
% 2.38/1.01  --bmc1_ucm                              false
% 2.38/1.01  --bmc1_add_unsat_core                   none
% 2.38/1.01  --bmc1_unsat_core_children              false
% 2.38/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.38/1.01  --bmc1_out_stat                         full
% 2.38/1.01  --bmc1_ground_init                      false
% 2.38/1.01  --bmc1_pre_inst_next_state              false
% 2.38/1.01  --bmc1_pre_inst_state                   false
% 2.38/1.01  --bmc1_pre_inst_reach_state             false
% 2.38/1.01  --bmc1_out_unsat_core                   false
% 2.38/1.01  --bmc1_aig_witness_out                  false
% 2.38/1.01  --bmc1_verbose                          false
% 2.38/1.01  --bmc1_dump_clauses_tptp                false
% 2.38/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.38/1.01  --bmc1_dump_file                        -
% 2.38/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.38/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.38/1.01  --bmc1_ucm_extend_mode                  1
% 2.38/1.01  --bmc1_ucm_init_mode                    2
% 2.38/1.01  --bmc1_ucm_cone_mode                    none
% 2.38/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.38/1.01  --bmc1_ucm_relax_model                  4
% 2.38/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.38/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.38/1.01  --bmc1_ucm_layered_model                none
% 2.38/1.01  --bmc1_ucm_max_lemma_size               10
% 2.38/1.01  
% 2.38/1.01  ------ AIG Options
% 2.38/1.01  
% 2.38/1.01  --aig_mode                              false
% 2.38/1.01  
% 2.38/1.01  ------ Instantiation Options
% 2.38/1.01  
% 2.38/1.01  --instantiation_flag                    true
% 2.38/1.01  --inst_sos_flag                         false
% 2.38/1.01  --inst_sos_phase                        true
% 2.38/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.38/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.38/1.01  --inst_lit_sel_side                     num_symb
% 2.38/1.01  --inst_solver_per_active                1400
% 2.38/1.01  --inst_solver_calls_frac                1.
% 2.38/1.01  --inst_passive_queue_type               priority_queues
% 2.38/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.38/1.01  --inst_passive_queues_freq              [25;2]
% 2.38/1.01  --inst_dismatching                      true
% 2.38/1.01  --inst_eager_unprocessed_to_passive     true
% 2.38/1.01  --inst_prop_sim_given                   true
% 2.38/1.01  --inst_prop_sim_new                     false
% 2.38/1.01  --inst_subs_new                         false
% 2.38/1.01  --inst_eq_res_simp                      false
% 2.38/1.01  --inst_subs_given                       false
% 2.38/1.01  --inst_orphan_elimination               true
% 2.38/1.01  --inst_learning_loop_flag               true
% 2.38/1.01  --inst_learning_start                   3000
% 2.38/1.01  --inst_learning_factor                  2
% 2.38/1.01  --inst_start_prop_sim_after_learn       3
% 2.38/1.01  --inst_sel_renew                        solver
% 2.38/1.01  --inst_lit_activity_flag                true
% 2.38/1.01  --inst_restr_to_given                   false
% 2.38/1.01  --inst_activity_threshold               500
% 2.38/1.01  --inst_out_proof                        true
% 2.38/1.01  
% 2.38/1.01  ------ Resolution Options
% 2.38/1.01  
% 2.38/1.01  --resolution_flag                       true
% 2.38/1.01  --res_lit_sel                           adaptive
% 2.38/1.01  --res_lit_sel_side                      none
% 2.38/1.01  --res_ordering                          kbo
% 2.38/1.01  --res_to_prop_solver                    active
% 2.38/1.01  --res_prop_simpl_new                    false
% 2.38/1.01  --res_prop_simpl_given                  true
% 2.38/1.01  --res_passive_queue_type                priority_queues
% 2.38/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.38/1.01  --res_passive_queues_freq               [15;5]
% 2.38/1.01  --res_forward_subs                      full
% 2.38/1.01  --res_backward_subs                     full
% 2.38/1.01  --res_forward_subs_resolution           true
% 2.38/1.01  --res_backward_subs_resolution          true
% 2.38/1.01  --res_orphan_elimination                true
% 2.38/1.01  --res_time_limit                        2.
% 2.38/1.01  --res_out_proof                         true
% 2.38/1.01  
% 2.38/1.01  ------ Superposition Options
% 2.38/1.01  
% 2.38/1.01  --superposition_flag                    true
% 2.38/1.01  --sup_passive_queue_type                priority_queues
% 2.38/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.38/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.38/1.01  --demod_completeness_check              fast
% 2.38/1.01  --demod_use_ground                      true
% 2.38/1.01  --sup_to_prop_solver                    passive
% 2.38/1.01  --sup_prop_simpl_new                    true
% 2.38/1.01  --sup_prop_simpl_given                  true
% 2.38/1.01  --sup_fun_splitting                     false
% 2.38/1.01  --sup_smt_interval                      50000
% 2.38/1.01  
% 2.38/1.01  ------ Superposition Simplification Setup
% 2.38/1.01  
% 2.38/1.01  --sup_indices_passive                   []
% 2.38/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.38/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.01  --sup_full_bw                           [BwDemod]
% 2.38/1.01  --sup_immed_triv                        [TrivRules]
% 2.38/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.38/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.01  --sup_immed_bw_main                     []
% 2.38/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.38/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.01  
% 2.38/1.01  ------ Combination Options
% 2.38/1.01  
% 2.38/1.01  --comb_res_mult                         3
% 2.38/1.01  --comb_sup_mult                         2
% 2.38/1.01  --comb_inst_mult                        10
% 2.38/1.01  
% 2.38/1.01  ------ Debug Options
% 2.38/1.01  
% 2.38/1.01  --dbg_backtrace                         false
% 2.38/1.01  --dbg_dump_prop_clauses                 false
% 2.38/1.01  --dbg_dump_prop_clauses_file            -
% 2.38/1.01  --dbg_out_stat                          false
% 2.38/1.01  ------ Parsing...
% 2.38/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.38/1.01  
% 2.38/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.38/1.01  
% 2.38/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.38/1.01  
% 2.38/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.38/1.01  ------ Proving...
% 2.38/1.01  ------ Problem Properties 
% 2.38/1.01  
% 2.38/1.01  
% 2.38/1.01  clauses                                 32
% 2.38/1.01  conjectures                             18
% 2.38/1.02  EPR                                     16
% 2.38/1.02  Horn                                    23
% 2.38/1.02  unary                                   16
% 2.38/1.02  binary                                  4
% 2.38/1.02  lits                                    118
% 2.38/1.02  lits eq                                 11
% 2.38/1.02  fd_pure                                 0
% 2.38/1.02  fd_pseudo                               0
% 2.38/1.02  fd_cond                                 0
% 2.38/1.02  fd_pseudo_cond                          0
% 2.38/1.02  AC symbols                              0
% 2.38/1.02  
% 2.38/1.02  ------ Schedule dynamic 5 is on 
% 2.38/1.02  
% 2.38/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  ------ 
% 2.38/1.02  Current options:
% 2.38/1.02  ------ 
% 2.38/1.02  
% 2.38/1.02  ------ Input Options
% 2.38/1.02  
% 2.38/1.02  --out_options                           all
% 2.38/1.02  --tptp_safe_out                         true
% 2.38/1.02  --problem_path                          ""
% 2.38/1.02  --include_path                          ""
% 2.38/1.02  --clausifier                            res/vclausify_rel
% 2.38/1.02  --clausifier_options                    --mode clausify
% 2.38/1.02  --stdin                                 false
% 2.38/1.02  --stats_out                             all
% 2.38/1.02  
% 2.38/1.02  ------ General Options
% 2.38/1.02  
% 2.38/1.02  --fof                                   false
% 2.38/1.02  --time_out_real                         305.
% 2.38/1.02  --time_out_virtual                      -1.
% 2.38/1.02  --symbol_type_check                     false
% 2.38/1.02  --clausify_out                          false
% 2.38/1.02  --sig_cnt_out                           false
% 2.38/1.02  --trig_cnt_out                          false
% 2.38/1.02  --trig_cnt_out_tolerance                1.
% 2.38/1.02  --trig_cnt_out_sk_spl                   false
% 2.38/1.02  --abstr_cl_out                          false
% 2.38/1.02  
% 2.38/1.02  ------ Global Options
% 2.38/1.02  
% 2.38/1.02  --schedule                              default
% 2.38/1.02  --add_important_lit                     false
% 2.38/1.02  --prop_solver_per_cl                    1000
% 2.38/1.02  --min_unsat_core                        false
% 2.38/1.02  --soft_assumptions                      false
% 2.38/1.02  --soft_lemma_size                       3
% 2.38/1.02  --prop_impl_unit_size                   0
% 2.38/1.02  --prop_impl_unit                        []
% 2.38/1.02  --share_sel_clauses                     true
% 2.38/1.02  --reset_solvers                         false
% 2.38/1.02  --bc_imp_inh                            [conj_cone]
% 2.38/1.02  --conj_cone_tolerance                   3.
% 2.38/1.02  --extra_neg_conj                        none
% 2.38/1.02  --large_theory_mode                     true
% 2.38/1.02  --prolific_symb_bound                   200
% 2.38/1.02  --lt_threshold                          2000
% 2.38/1.02  --clause_weak_htbl                      true
% 2.38/1.02  --gc_record_bc_elim                     false
% 2.38/1.02  
% 2.38/1.02  ------ Preprocessing Options
% 2.38/1.02  
% 2.38/1.02  --preprocessing_flag                    true
% 2.38/1.02  --time_out_prep_mult                    0.1
% 2.38/1.02  --splitting_mode                        input
% 2.38/1.02  --splitting_grd                         true
% 2.38/1.02  --splitting_cvd                         false
% 2.38/1.02  --splitting_cvd_svl                     false
% 2.38/1.02  --splitting_nvd                         32
% 2.38/1.02  --sub_typing                            true
% 2.38/1.02  --prep_gs_sim                           true
% 2.38/1.02  --prep_unflatten                        true
% 2.38/1.02  --prep_res_sim                          true
% 2.38/1.02  --prep_upred                            true
% 2.38/1.02  --prep_sem_filter                       exhaustive
% 2.38/1.02  --prep_sem_filter_out                   false
% 2.38/1.02  --pred_elim                             true
% 2.38/1.02  --res_sim_input                         true
% 2.38/1.02  --eq_ax_congr_red                       true
% 2.38/1.02  --pure_diseq_elim                       true
% 2.38/1.02  --brand_transform                       false
% 2.38/1.02  --non_eq_to_eq                          false
% 2.38/1.02  --prep_def_merge                        true
% 2.38/1.02  --prep_def_merge_prop_impl              false
% 2.38/1.02  --prep_def_merge_mbd                    true
% 2.38/1.02  --prep_def_merge_tr_red                 false
% 2.38/1.02  --prep_def_merge_tr_cl                  false
% 2.38/1.02  --smt_preprocessing                     true
% 2.38/1.02  --smt_ac_axioms                         fast
% 2.38/1.02  --preprocessed_out                      false
% 2.38/1.02  --preprocessed_stats                    false
% 2.38/1.02  
% 2.38/1.02  ------ Abstraction refinement Options
% 2.38/1.02  
% 2.38/1.02  --abstr_ref                             []
% 2.38/1.02  --abstr_ref_prep                        false
% 2.38/1.02  --abstr_ref_until_sat                   false
% 2.38/1.02  --abstr_ref_sig_restrict                funpre
% 2.38/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.38/1.02  --abstr_ref_under                       []
% 2.38/1.02  
% 2.38/1.02  ------ SAT Options
% 2.38/1.02  
% 2.38/1.02  --sat_mode                              false
% 2.38/1.02  --sat_fm_restart_options                ""
% 2.38/1.02  --sat_gr_def                            false
% 2.38/1.02  --sat_epr_types                         true
% 2.38/1.02  --sat_non_cyclic_types                  false
% 2.38/1.02  --sat_finite_models                     false
% 2.38/1.02  --sat_fm_lemmas                         false
% 2.38/1.02  --sat_fm_prep                           false
% 2.38/1.02  --sat_fm_uc_incr                        true
% 2.38/1.02  --sat_out_model                         small
% 2.38/1.02  --sat_out_clauses                       false
% 2.38/1.02  
% 2.38/1.02  ------ QBF Options
% 2.38/1.02  
% 2.38/1.02  --qbf_mode                              false
% 2.38/1.02  --qbf_elim_univ                         false
% 2.38/1.02  --qbf_dom_inst                          none
% 2.38/1.02  --qbf_dom_pre_inst                      false
% 2.38/1.02  --qbf_sk_in                             false
% 2.38/1.02  --qbf_pred_elim                         true
% 2.38/1.02  --qbf_split                             512
% 2.38/1.02  
% 2.38/1.02  ------ BMC1 Options
% 2.38/1.02  
% 2.38/1.02  --bmc1_incremental                      false
% 2.38/1.02  --bmc1_axioms                           reachable_all
% 2.38/1.02  --bmc1_min_bound                        0
% 2.38/1.02  --bmc1_max_bound                        -1
% 2.38/1.02  --bmc1_max_bound_default                -1
% 2.38/1.02  --bmc1_symbol_reachability              true
% 2.38/1.02  --bmc1_property_lemmas                  false
% 2.38/1.02  --bmc1_k_induction                      false
% 2.38/1.02  --bmc1_non_equiv_states                 false
% 2.38/1.02  --bmc1_deadlock                         false
% 2.38/1.02  --bmc1_ucm                              false
% 2.38/1.02  --bmc1_add_unsat_core                   none
% 2.38/1.02  --bmc1_unsat_core_children              false
% 2.38/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.38/1.02  --bmc1_out_stat                         full
% 2.38/1.02  --bmc1_ground_init                      false
% 2.38/1.02  --bmc1_pre_inst_next_state              false
% 2.38/1.02  --bmc1_pre_inst_state                   false
% 2.38/1.02  --bmc1_pre_inst_reach_state             false
% 2.38/1.02  --bmc1_out_unsat_core                   false
% 2.38/1.02  --bmc1_aig_witness_out                  false
% 2.38/1.02  --bmc1_verbose                          false
% 2.38/1.02  --bmc1_dump_clauses_tptp                false
% 2.38/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.38/1.02  --bmc1_dump_file                        -
% 2.38/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.38/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.38/1.02  --bmc1_ucm_extend_mode                  1
% 2.38/1.02  --bmc1_ucm_init_mode                    2
% 2.38/1.02  --bmc1_ucm_cone_mode                    none
% 2.38/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.38/1.02  --bmc1_ucm_relax_model                  4
% 2.38/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.38/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.38/1.02  --bmc1_ucm_layered_model                none
% 2.38/1.02  --bmc1_ucm_max_lemma_size               10
% 2.38/1.02  
% 2.38/1.02  ------ AIG Options
% 2.38/1.02  
% 2.38/1.02  --aig_mode                              false
% 2.38/1.02  
% 2.38/1.02  ------ Instantiation Options
% 2.38/1.02  
% 2.38/1.02  --instantiation_flag                    true
% 2.38/1.02  --inst_sos_flag                         false
% 2.38/1.02  --inst_sos_phase                        true
% 2.38/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.38/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.38/1.02  --inst_lit_sel_side                     none
% 2.38/1.02  --inst_solver_per_active                1400
% 2.38/1.02  --inst_solver_calls_frac                1.
% 2.38/1.02  --inst_passive_queue_type               priority_queues
% 2.38/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.38/1.02  --inst_passive_queues_freq              [25;2]
% 2.38/1.02  --inst_dismatching                      true
% 2.38/1.02  --inst_eager_unprocessed_to_passive     true
% 2.38/1.02  --inst_prop_sim_given                   true
% 2.38/1.02  --inst_prop_sim_new                     false
% 2.38/1.02  --inst_subs_new                         false
% 2.38/1.02  --inst_eq_res_simp                      false
% 2.38/1.02  --inst_subs_given                       false
% 2.38/1.02  --inst_orphan_elimination               true
% 2.38/1.02  --inst_learning_loop_flag               true
% 2.38/1.02  --inst_learning_start                   3000
% 2.38/1.02  --inst_learning_factor                  2
% 2.38/1.02  --inst_start_prop_sim_after_learn       3
% 2.38/1.02  --inst_sel_renew                        solver
% 2.38/1.02  --inst_lit_activity_flag                true
% 2.38/1.02  --inst_restr_to_given                   false
% 2.38/1.02  --inst_activity_threshold               500
% 2.38/1.02  --inst_out_proof                        true
% 2.38/1.02  
% 2.38/1.02  ------ Resolution Options
% 2.38/1.02  
% 2.38/1.02  --resolution_flag                       false
% 2.38/1.02  --res_lit_sel                           adaptive
% 2.38/1.02  --res_lit_sel_side                      none
% 2.38/1.02  --res_ordering                          kbo
% 2.38/1.02  --res_to_prop_solver                    active
% 2.38/1.02  --res_prop_simpl_new                    false
% 2.38/1.02  --res_prop_simpl_given                  true
% 2.38/1.02  --res_passive_queue_type                priority_queues
% 2.38/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.38/1.02  --res_passive_queues_freq               [15;5]
% 2.38/1.02  --res_forward_subs                      full
% 2.38/1.02  --res_backward_subs                     full
% 2.38/1.02  --res_forward_subs_resolution           true
% 2.38/1.02  --res_backward_subs_resolution          true
% 2.38/1.02  --res_orphan_elimination                true
% 2.38/1.02  --res_time_limit                        2.
% 2.38/1.02  --res_out_proof                         true
% 2.38/1.02  
% 2.38/1.02  ------ Superposition Options
% 2.38/1.02  
% 2.38/1.02  --superposition_flag                    true
% 2.38/1.02  --sup_passive_queue_type                priority_queues
% 2.38/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.38/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.38/1.02  --demod_completeness_check              fast
% 2.38/1.02  --demod_use_ground                      true
% 2.38/1.02  --sup_to_prop_solver                    passive
% 2.38/1.02  --sup_prop_simpl_new                    true
% 2.38/1.02  --sup_prop_simpl_given                  true
% 2.38/1.02  --sup_fun_splitting                     false
% 2.38/1.02  --sup_smt_interval                      50000
% 2.38/1.02  
% 2.38/1.02  ------ Superposition Simplification Setup
% 2.38/1.02  
% 2.38/1.02  --sup_indices_passive                   []
% 2.38/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.38/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.02  --sup_full_bw                           [BwDemod]
% 2.38/1.02  --sup_immed_triv                        [TrivRules]
% 2.38/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.38/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.02  --sup_immed_bw_main                     []
% 2.38/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.38/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.02  
% 2.38/1.02  ------ Combination Options
% 2.38/1.02  
% 2.38/1.02  --comb_res_mult                         3
% 2.38/1.02  --comb_sup_mult                         2
% 2.38/1.02  --comb_inst_mult                        10
% 2.38/1.02  
% 2.38/1.02  ------ Debug Options
% 2.38/1.02  
% 2.38/1.02  --dbg_backtrace                         false
% 2.38/1.02  --dbg_dump_prop_clauses                 false
% 2.38/1.02  --dbg_dump_prop_clauses_file            -
% 2.38/1.02  --dbg_out_stat                          false
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  ------ Proving...
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  % SZS status Theorem for theBenchmark.p
% 2.38/1.02  
% 2.38/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.38/1.02  
% 2.38/1.02  fof(f13,conjecture,(
% 2.38/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f14,negated_conjecture,(
% 2.38/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 2.38/1.02    inference(negated_conjecture,[],[f13])).
% 2.38/1.02  
% 2.38/1.02  fof(f36,plain,(
% 2.38/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.38/1.02    inference(ennf_transformation,[],[f14])).
% 2.38/1.02  
% 2.38/1.02  fof(f37,plain,(
% 2.38/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.38/1.02    inference(flattening,[],[f36])).
% 2.38/1.02  
% 2.38/1.02  fof(f41,plain,(
% 2.38/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.38/1.02    inference(nnf_transformation,[],[f37])).
% 2.38/1.02  
% 2.38/1.02  fof(f42,plain,(
% 2.38/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.38/1.02    inference(flattening,[],[f41])).
% 2.38/1.02  
% 2.38/1.02  fof(f49,plain,(
% 2.38/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | r1_tmap_1(X3,X0,X4,X5)) & sK7 = X5 & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f48,plain,(
% 2.38/1.02    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,sK6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,sK6)) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f47,plain,(
% 2.38/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X6) | ~r1_tmap_1(X3,X0,sK5,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X6) | r1_tmap_1(X3,X0,sK5,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f46,plain,(
% 2.38/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X6) | ~r1_tmap_1(sK4,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X6) | r1_tmap_1(sK4,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_pre_topc(X2,sK4) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X1) & ~v2_struct_0(sK4))) )),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f45,plain,(
% 2.38/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK3,X3) & m1_pre_topc(sK3,X1) & v1_tsep_1(sK3,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f44,plain,(
% 2.38/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK2) & v1_tsep_1(X2,sK2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f43,plain,(
% 2.38/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f50,plain,(
% 2.38/1.02    (((((((~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | ~r1_tmap_1(sK4,sK1,sK5,sK6)) & (r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | r1_tmap_1(sK4,sK1,sK5,sK6)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK3,sK2) & v1_tsep_1(sK3,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.38/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f42,f49,f48,f47,f46,f45,f44,f43])).
% 2.38/1.02  
% 2.38/1.02  fof(f81,plain,(
% 2.38/1.02    m1_pre_topc(sK3,sK4)),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f75,plain,(
% 2.38/1.02    m1_pre_topc(sK4,sK2)),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f1,axiom,(
% 2.38/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f15,plain,(
% 2.38/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 2.38/1.02    inference(unused_predicate_definition_removal,[],[f1])).
% 2.38/1.02  
% 2.38/1.02  fof(f16,plain,(
% 2.38/1.02    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 2.38/1.02    inference(ennf_transformation,[],[f15])).
% 2.38/1.02  
% 2.38/1.02  fof(f38,plain,(
% 2.38/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f39,plain,(
% 2.38/1.02    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.38/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f38])).
% 2.38/1.02  
% 2.38/1.02  fof(f51,plain,(
% 2.38/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f39])).
% 2.38/1.02  
% 2.38/1.02  fof(f9,axiom,(
% 2.38/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f29,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.38/1.02    inference(ennf_transformation,[],[f9])).
% 2.38/1.02  
% 2.38/1.02  fof(f61,plain,(
% 2.38/1.02    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f29])).
% 2.38/1.02  
% 2.38/1.02  fof(f2,axiom,(
% 2.38/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f17,plain,(
% 2.38/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.38/1.02    inference(ennf_transformation,[],[f2])).
% 2.38/1.02  
% 2.38/1.02  fof(f53,plain,(
% 2.38/1.02    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.38/1.02    inference(cnf_transformation,[],[f17])).
% 2.38/1.02  
% 2.38/1.02  fof(f52,plain,(
% 2.38/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f39])).
% 2.38/1.02  
% 2.38/1.02  fof(f8,axiom,(
% 2.38/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f27,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.38/1.02    inference(ennf_transformation,[],[f8])).
% 2.38/1.02  
% 2.38/1.02  fof(f28,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.38/1.02    inference(flattening,[],[f27])).
% 2.38/1.02  
% 2.38/1.02  fof(f59,plain,(
% 2.38/1.02    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f28])).
% 2.38/1.02  
% 2.38/1.02  fof(f4,axiom,(
% 2.38/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f20,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.38/1.02    inference(ennf_transformation,[],[f4])).
% 2.38/1.02  
% 2.38/1.02  fof(f55,plain,(
% 2.38/1.02    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f20])).
% 2.38/1.02  
% 2.38/1.02  fof(f12,axiom,(
% 2.38/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f34,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.38/1.02    inference(ennf_transformation,[],[f12])).
% 2.38/1.02  
% 2.38/1.02  fof(f35,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.38/1.02    inference(flattening,[],[f34])).
% 2.38/1.02  
% 2.38/1.02  fof(f65,plain,(
% 2.38/1.02    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f35])).
% 2.38/1.02  
% 2.38/1.02  fof(f69,plain,(
% 2.38/1.02    ~v2_struct_0(sK2)),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f70,plain,(
% 2.38/1.02    v2_pre_topc(sK2)),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f71,plain,(
% 2.38/1.02    l1_pre_topc(sK2)),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f74,plain,(
% 2.38/1.02    ~v2_struct_0(sK4)),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f7,axiom,(
% 2.38/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f25,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.38/1.02    inference(ennf_transformation,[],[f7])).
% 2.38/1.02  
% 2.38/1.02  fof(f26,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.38/1.02    inference(flattening,[],[f25])).
% 2.38/1.02  
% 2.38/1.02  fof(f58,plain,(
% 2.38/1.02    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f26])).
% 2.38/1.02  
% 2.38/1.02  fof(f77,plain,(
% 2.38/1.02    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f76,plain,(
% 2.38/1.02    v1_funct_1(sK5)),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f66,plain,(
% 2.38/1.02    ~v2_struct_0(sK1)),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f67,plain,(
% 2.38/1.02    v2_pre_topc(sK1)),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f68,plain,(
% 2.38/1.02    l1_pre_topc(sK1)),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f78,plain,(
% 2.38/1.02    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f6,axiom,(
% 2.38/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f23,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.38/1.02    inference(ennf_transformation,[],[f6])).
% 2.38/1.02  
% 2.38/1.02  fof(f24,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.38/1.02    inference(flattening,[],[f23])).
% 2.38/1.02  
% 2.38/1.02  fof(f57,plain,(
% 2.38/1.02    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f24])).
% 2.38/1.02  
% 2.38/1.02  fof(f3,axiom,(
% 2.38/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f18,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.38/1.02    inference(ennf_transformation,[],[f3])).
% 2.38/1.02  
% 2.38/1.02  fof(f19,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.38/1.02    inference(flattening,[],[f18])).
% 2.38/1.02  
% 2.38/1.02  fof(f54,plain,(
% 2.38/1.02    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f19])).
% 2.38/1.02  
% 2.38/1.02  fof(f86,plain,(
% 2.38/1.02    ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | ~r1_tmap_1(sK4,sK1,sK5,sK6)),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f84,plain,(
% 2.38/1.02    sK6 = sK7),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f72,plain,(
% 2.38/1.02    ~v2_struct_0(sK3)),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f83,plain,(
% 2.38/1.02    m1_subset_1(sK7,u1_struct_0(sK3))),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f11,axiom,(
% 2.38/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f32,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.38/1.02    inference(ennf_transformation,[],[f11])).
% 2.38/1.02  
% 2.38/1.02  fof(f33,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.38/1.02    inference(flattening,[],[f32])).
% 2.38/1.02  
% 2.38/1.02  fof(f40,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4))) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.38/1.02    inference(nnf_transformation,[],[f33])).
% 2.38/1.02  
% 2.38/1.02  fof(f63,plain,(
% 2.38/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f40])).
% 2.38/1.02  
% 2.38/1.02  fof(f89,plain,(
% 2.38/1.02    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.38/1.02    inference(equality_resolution,[],[f63])).
% 2.38/1.02  
% 2.38/1.02  fof(f10,axiom,(
% 2.38/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f30,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.38/1.02    inference(ennf_transformation,[],[f10])).
% 2.38/1.02  
% 2.38/1.02  fof(f31,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.38/1.02    inference(flattening,[],[f30])).
% 2.38/1.02  
% 2.38/1.02  fof(f62,plain,(
% 2.38/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f31])).
% 2.38/1.02  
% 2.38/1.02  fof(f87,plain,(
% 2.38/1.02    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.38/1.02    inference(equality_resolution,[],[f62])).
% 2.38/1.02  
% 2.38/1.02  fof(f5,axiom,(
% 2.38/1.02    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f21,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.38/1.02    inference(ennf_transformation,[],[f5])).
% 2.38/1.02  
% 2.38/1.02  fof(f22,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.38/1.02    inference(flattening,[],[f21])).
% 2.38/1.02  
% 2.38/1.02  fof(f56,plain,(
% 2.38/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f22])).
% 2.38/1.02  
% 2.38/1.02  fof(f85,plain,(
% 2.38/1.02    r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | r1_tmap_1(sK4,sK1,sK5,sK6)),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  fof(f64,plain,(
% 2.38/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f40])).
% 2.38/1.02  
% 2.38/1.02  fof(f88,plain,(
% 2.38/1.02    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.38/1.02    inference(equality_resolution,[],[f64])).
% 2.38/1.02  
% 2.38/1.02  fof(f79,plain,(
% 2.38/1.02    v1_tsep_1(sK3,sK2)),
% 2.38/1.02    inference(cnf_transformation,[],[f50])).
% 2.38/1.02  
% 2.38/1.02  cnf(c_20,negated_conjecture,
% 2.38/1.02      ( m1_pre_topc(sK3,sK4) ),
% 2.38/1.02      inference(cnf_transformation,[],[f81]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1316,negated_conjecture,
% 2.38/1.02      ( m1_pre_topc(sK3,sK4) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_20]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2068,plain,
% 2.38/1.02      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1316]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_26,negated_conjecture,
% 2.38/1.02      ( m1_pre_topc(sK4,sK2) ),
% 2.38/1.02      inference(cnf_transformation,[],[f75]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1312,negated_conjecture,
% 2.38/1.02      ( m1_pre_topc(sK4,sK2) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_26]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2072,plain,
% 2.38/1.02      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1312]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1,plain,
% 2.38/1.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1330,plain,
% 2.38/1.02      ( r2_hidden(sK0(X0_54,X1_54),X0_54) | r1_tarski(X0_54,X1_54) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2055,plain,
% 2.38/1.02      ( r2_hidden(sK0(X0_54,X1_54),X0_54) = iProver_top
% 2.38/1.02      | r1_tarski(X0_54,X1_54) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1330]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_10,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.38/1.02      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.38/1.02      | ~ l1_pre_topc(X1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1323,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.38/1.02      | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53)))
% 2.38/1.02      | ~ l1_pre_topc(X1_53) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2062,plain,
% 2.38/1.02      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.38/1.02      | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53))) = iProver_top
% 2.38/1.02      | l1_pre_topc(X1_53) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1323]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2,plain,
% 2.38/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.38/1.02      | ~ r2_hidden(X2,X0)
% 2.38/1.02      | r2_hidden(X2,X1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1329,plain,
% 2.38/1.02      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 2.38/1.02      | ~ r2_hidden(X0_55,X0_54)
% 2.38/1.02      | r2_hidden(X0_55,X1_54) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2056,plain,
% 2.38/1.02      ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
% 2.38/1.02      | r2_hidden(X0_55,X0_54) != iProver_top
% 2.38/1.02      | r2_hidden(X0_55,X1_54) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1329]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2978,plain,
% 2.38/1.02      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.38/1.02      | r2_hidden(X0_55,u1_struct_0(X0_53)) != iProver_top
% 2.38/1.02      | r2_hidden(X0_55,u1_struct_0(X1_53)) = iProver_top
% 2.38/1.02      | l1_pre_topc(X1_53) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_2062,c_2056]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3753,plain,
% 2.38/1.02      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.38/1.02      | r2_hidden(sK0(u1_struct_0(X0_53),X0_54),u1_struct_0(X1_53)) = iProver_top
% 2.38/1.02      | r1_tarski(u1_struct_0(X0_53),X0_54) = iProver_top
% 2.38/1.02      | l1_pre_topc(X1_53) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_2055,c_2978]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_0,plain,
% 2.38/1.02      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1331,plain,
% 2.38/1.02      ( ~ r2_hidden(sK0(X0_54,X1_54),X1_54) | r1_tarski(X0_54,X1_54) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2054,plain,
% 2.38/1.02      ( r2_hidden(sK0(X0_54,X1_54),X1_54) != iProver_top
% 2.38/1.02      | r1_tarski(X0_54,X1_54) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1331]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3828,plain,
% 2.38/1.02      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.38/1.02      | r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53)) = iProver_top
% 2.38/1.02      | l1_pre_topc(X1_53) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_3753,c_2054]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_9,plain,
% 2.38/1.02      ( ~ v1_tsep_1(X0,X1)
% 2.38/1.02      | v1_tsep_1(X0,X2)
% 2.38/1.02      | ~ m1_pre_topc(X0,X1)
% 2.38/1.02      | ~ m1_pre_topc(X2,X1)
% 2.38/1.02      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1324,plain,
% 2.38/1.02      ( ~ v1_tsep_1(X0_53,X1_53)
% 2.38/1.02      | v1_tsep_1(X0_53,X2_53)
% 2.38/1.02      | ~ m1_pre_topc(X0_53,X1_53)
% 2.38/1.02      | ~ m1_pre_topc(X2_53,X1_53)
% 2.38/1.02      | ~ r1_tarski(u1_struct_0(X0_53),u1_struct_0(X2_53))
% 2.38/1.02      | v2_struct_0(X1_53)
% 2.38/1.02      | v2_struct_0(X2_53)
% 2.38/1.02      | ~ l1_pre_topc(X1_53)
% 2.38/1.02      | ~ v2_pre_topc(X1_53) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2061,plain,
% 2.38/1.02      ( v1_tsep_1(X0_53,X1_53) != iProver_top
% 2.38/1.02      | v1_tsep_1(X0_53,X2_53) = iProver_top
% 2.38/1.02      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.38/1.02      | m1_pre_topc(X2_53,X1_53) != iProver_top
% 2.38/1.02      | r1_tarski(u1_struct_0(X0_53),u1_struct_0(X2_53)) != iProver_top
% 2.38/1.02      | v2_struct_0(X1_53) = iProver_top
% 2.38/1.02      | v2_struct_0(X2_53) = iProver_top
% 2.38/1.02      | l1_pre_topc(X1_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X1_53) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1324]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4259,plain,
% 2.38/1.02      ( v1_tsep_1(X0_53,X1_53) != iProver_top
% 2.38/1.02      | v1_tsep_1(X0_53,X2_53) = iProver_top
% 2.38/1.02      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.38/1.02      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.38/1.02      | m1_pre_topc(X2_53,X1_53) != iProver_top
% 2.38/1.02      | v2_struct_0(X2_53) = iProver_top
% 2.38/1.02      | v2_struct_0(X1_53) = iProver_top
% 2.38/1.02      | l1_pre_topc(X2_53) != iProver_top
% 2.38/1.02      | l1_pre_topc(X1_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X1_53) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_3828,c_2061]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1327,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.38/1.02      | ~ l1_pre_topc(X1_53)
% 2.38/1.02      | l1_pre_topc(X0_53) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2058,plain,
% 2.38/1.02      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.38/1.02      | l1_pre_topc(X1_53) != iProver_top
% 2.38/1.02      | l1_pre_topc(X0_53) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1327]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_14,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.38/1.02      | ~ m1_pre_topc(X2,X0)
% 2.38/1.02      | m1_pre_topc(X2,X1)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1322,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.38/1.02      | ~ m1_pre_topc(X2_53,X0_53)
% 2.38/1.02      | m1_pre_topc(X2_53,X1_53)
% 2.38/1.02      | ~ l1_pre_topc(X1_53)
% 2.38/1.02      | ~ v2_pre_topc(X1_53) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_14]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2063,plain,
% 2.38/1.02      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.38/1.02      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.38/1.02      | m1_pre_topc(X2_53,X1_53) = iProver_top
% 2.38/1.02      | l1_pre_topc(X1_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X1_53) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1322]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4870,plain,
% 2.38/1.02      ( v1_tsep_1(X0_53,X1_53) != iProver_top
% 2.38/1.02      | v1_tsep_1(X0_53,X2_53) = iProver_top
% 2.38/1.02      | m1_pre_topc(X2_53,X1_53) != iProver_top
% 2.38/1.02      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.38/1.02      | v2_struct_0(X1_53) = iProver_top
% 2.38/1.02      | v2_struct_0(X2_53) = iProver_top
% 2.38/1.02      | l1_pre_topc(X1_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X1_53) != iProver_top ),
% 2.38/1.02      inference(forward_subsumption_resolution,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_4259,c_2058,c_2063]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4874,plain,
% 2.38/1.02      ( v1_tsep_1(X0_53,sK4) = iProver_top
% 2.38/1.02      | v1_tsep_1(X0_53,sK2) != iProver_top
% 2.38/1.02      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.38/1.02      | v2_struct_0(sK4) = iProver_top
% 2.38/1.02      | v2_struct_0(sK2) = iProver_top
% 2.38/1.02      | l1_pre_topc(sK2) != iProver_top
% 2.38/1.02      | v2_pre_topc(sK2) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_2072,c_4870]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_32,negated_conjecture,
% 2.38/1.02      ( ~ v2_struct_0(sK2) ),
% 2.38/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_39,plain,
% 2.38/1.02      ( v2_struct_0(sK2) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_31,negated_conjecture,
% 2.38/1.02      ( v2_pre_topc(sK2) ),
% 2.38/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_40,plain,
% 2.38/1.02      ( v2_pre_topc(sK2) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_30,negated_conjecture,
% 2.38/1.02      ( l1_pre_topc(sK2) ),
% 2.38/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_41,plain,
% 2.38/1.02      ( l1_pre_topc(sK2) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_27,negated_conjecture,
% 2.38/1.02      ( ~ v2_struct_0(sK4) ),
% 2.38/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_44,plain,
% 2.38/1.02      ( v2_struct_0(sK4) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_5097,plain,
% 2.38/1.02      ( v1_tsep_1(X0_53,sK4) = iProver_top
% 2.38/1.02      | v1_tsep_1(X0_53,sK2) != iProver_top
% 2.38/1.02      | m1_pre_topc(X0_53,sK4) != iProver_top ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_4874,c_39,c_40,c_41,c_44]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_5106,plain,
% 2.38/1.02      ( v1_tsep_1(sK3,sK4) = iProver_top
% 2.38/1.02      | v1_tsep_1(sK3,sK2) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_2068,c_5097]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_7,plain,
% 2.38/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.38/1.02      | ~ m1_pre_topc(X3,X4)
% 2.38/1.02      | ~ m1_pre_topc(X3,X1)
% 2.38/1.02      | ~ m1_pre_topc(X1,X4)
% 2.38/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.38/1.02      | ~ v1_funct_1(X0)
% 2.38/1.02      | v2_struct_0(X4)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | ~ l1_pre_topc(X4)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X4)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_24,negated_conjecture,
% 2.38/1.02      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
% 2.38/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_759,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.38/1.02      | ~ m1_pre_topc(X0,X2)
% 2.38/1.02      | ~ m1_pre_topc(X1,X2)
% 2.38/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 2.38/1.02      | ~ v1_funct_1(X3)
% 2.38/1.02      | v2_struct_0(X4)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | ~ l1_pre_topc(X4)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X4)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X4) != u1_struct_0(sK1)
% 2.38/1.02      | sK5 != X3 ),
% 2.38/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_760,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.38/1.02      | ~ m1_pre_topc(X0,X2)
% 2.38/1.02      | ~ m1_pre_topc(X1,X2)
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.38/1.02      | ~ v1_funct_1(sK5)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | v2_struct_0(X3)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ l1_pre_topc(X3)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X3)
% 2.38/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(unflattening,[status(thm)],[c_759]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_25,negated_conjecture,
% 2.38/1.02      ( v1_funct_1(sK5) ),
% 2.38/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_764,plain,
% 2.38/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.38/1.02      | ~ m1_pre_topc(X1,X2)
% 2.38/1.02      | ~ m1_pre_topc(X0,X2)
% 2.38/1.02      | ~ m1_pre_topc(X0,X1)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | v2_struct_0(X3)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ l1_pre_topc(X3)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X3)
% 2.38/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_760,c_25]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_765,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.38/1.02      | ~ m1_pre_topc(X0,X2)
% 2.38/1.02      | ~ m1_pre_topc(X1,X2)
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | v2_struct_0(X3)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ l1_pre_topc(X3)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X3)
% 2.38/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(renaming,[status(thm)],[c_764]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_796,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.38/1.02      | ~ m1_pre_topc(X1,X2)
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | v2_struct_0(X3)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ l1_pre_topc(X3)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X3)
% 2.38/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(forward_subsumption_resolution,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_765,c_14]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1301,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.38/1.02      | ~ m1_pre_topc(X1_53,X2_53)
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X3_53))))
% 2.38/1.02      | v2_struct_0(X2_53)
% 2.38/1.02      | v2_struct_0(X3_53)
% 2.38/1.02      | ~ l1_pre_topc(X2_53)
% 2.38/1.02      | ~ l1_pre_topc(X3_53)
% 2.38/1.02      | ~ v2_pre_topc(X2_53)
% 2.38/1.02      | ~ v2_pre_topc(X3_53)
% 2.38/1.02      | k2_partfun1(u1_struct_0(X1_53),u1_struct_0(X3_53),sK5,u1_struct_0(X0_53)) = k3_tmap_1(X2_53,X3_53,X1_53,X0_53,sK5)
% 2.38/1.02      | u1_struct_0(X1_53) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X3_53) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_796]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2083,plain,
% 2.38/1.02      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK5,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,sK5)
% 2.38/1.02      | u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 2.38/1.02      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.38/1.02      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 2.38/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.38/1.02      | v2_struct_0(X3_53) = iProver_top
% 2.38/1.02      | v2_struct_0(X1_53) = iProver_top
% 2.38/1.02      | l1_pre_topc(X1_53) != iProver_top
% 2.38/1.02      | l1_pre_topc(X3_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X1_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X3_53) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1301]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4000,plain,
% 2.38/1.02      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK5,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK5)
% 2.38/1.02      | u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.38/1.02      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.38/1.02      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.38/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.38/1.02      | v2_struct_0(X2_53) = iProver_top
% 2.38/1.02      | v2_struct_0(sK1) = iProver_top
% 2.38/1.02      | l1_pre_topc(X2_53) != iProver_top
% 2.38/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.38/1.02      | v2_pre_topc(X2_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(sK1) != iProver_top ),
% 2.38/1.02      inference(equality_resolution,[status(thm)],[c_2083]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_35,negated_conjecture,
% 2.38/1.02      ( ~ v2_struct_0(sK1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_36,plain,
% 2.38/1.02      ( v2_struct_0(sK1) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_34,negated_conjecture,
% 2.38/1.02      ( v2_pre_topc(sK1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_37,plain,
% 2.38/1.02      ( v2_pre_topc(sK1) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_33,negated_conjecture,
% 2.38/1.02      ( l1_pre_topc(sK1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_38,plain,
% 2.38/1.02      ( l1_pre_topc(sK1) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4152,plain,
% 2.38/1.02      ( v2_pre_topc(X2_53) != iProver_top
% 2.38/1.02      | v2_struct_0(X2_53) = iProver_top
% 2.38/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.38/1.02      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.38/1.02      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.38/1.02      | u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.38/1.02      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK5,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK5)
% 2.38/1.02      | l1_pre_topc(X2_53) != iProver_top ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_4000,c_36,c_37,c_38]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4153,plain,
% 2.38/1.02      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK5,u1_struct_0(X1_53)) = k3_tmap_1(X2_53,sK1,X0_53,X1_53,sK5)
% 2.38/1.02      | u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.38/1.02      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.38/1.02      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.38/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.38/1.02      | v2_struct_0(X2_53) = iProver_top
% 2.38/1.02      | l1_pre_topc(X2_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X2_53) != iProver_top ),
% 2.38/1.02      inference(renaming,[status(thm)],[c_4152]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4164,plain,
% 2.38/1.02      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK4,X0_53,sK5)
% 2.38/1.02      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.38/1.02      | m1_pre_topc(sK4,X1_53) != iProver_top
% 2.38/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 2.38/1.02      | v2_struct_0(X1_53) = iProver_top
% 2.38/1.02      | l1_pre_topc(X1_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X1_53) != iProver_top ),
% 2.38/1.02      inference(equality_resolution,[status(thm)],[c_4153]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_23,negated_conjecture,
% 2.38/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
% 2.38/1.02      inference(cnf_transformation,[],[f78]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_48,plain,
% 2.38/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4424,plain,
% 2.38/1.02      ( m1_pre_topc(sK4,X1_53) != iProver_top
% 2.38/1.02      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.38/1.02      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK4,X0_53,sK5)
% 2.38/1.02      | v2_struct_0(X1_53) = iProver_top
% 2.38/1.02      | l1_pre_topc(X1_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X1_53) != iProver_top ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_4164,c_48]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4425,plain,
% 2.38/1.02      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK4,X0_53,sK5)
% 2.38/1.02      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.38/1.02      | m1_pre_topc(sK4,X1_53) != iProver_top
% 2.38/1.02      | v2_struct_0(X1_53) = iProver_top
% 2.38/1.02      | l1_pre_topc(X1_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X1_53) != iProver_top ),
% 2.38/1.02      inference(renaming,[status(thm)],[c_4424]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4436,plain,
% 2.38/1.02      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(X0_53,sK1,sK4,sK3,sK5)
% 2.38/1.02      | m1_pre_topc(sK4,X0_53) != iProver_top
% 2.38/1.02      | v2_struct_0(X0_53) = iProver_top
% 2.38/1.02      | l1_pre_topc(X0_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X0_53) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_2068,c_4425]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_6,plain,
% 2.38/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.38/1.02      | ~ m1_pre_topc(X3,X1)
% 2.38/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.38/1.02      | ~ v1_funct_1(X0)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.38/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_810,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.38/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.38/1.02      | ~ v1_funct_1(X2)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X3)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ l1_pre_topc(X3)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X3)
% 2.38/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X3) != u1_struct_0(sK1)
% 2.38/1.02      | sK5 != X2 ),
% 2.38/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_24]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_811,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.38/1.02      | ~ v1_funct_1(sK5)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(unflattening,[status(thm)],[c_810]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_815,plain,
% 2.38/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.38/1.02      | ~ m1_pre_topc(X0,X1)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_811,c_25]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_816,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(renaming,[status(thm)],[c_815]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1300,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X2_53))))
% 2.38/1.02      | v2_struct_0(X1_53)
% 2.38/1.02      | v2_struct_0(X2_53)
% 2.38/1.02      | ~ l1_pre_topc(X1_53)
% 2.38/1.02      | ~ l1_pre_topc(X2_53)
% 2.38/1.02      | ~ v2_pre_topc(X1_53)
% 2.38/1.02      | ~ v2_pre_topc(X2_53)
% 2.38/1.02      | k2_partfun1(u1_struct_0(X1_53),u1_struct_0(X2_53),sK5,u1_struct_0(X0_53)) = k2_tmap_1(X1_53,X2_53,sK5,X0_53)
% 2.38/1.02      | u1_struct_0(X1_53) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X2_53) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_816]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2084,plain,
% 2.38/1.02      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),sK5,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,sK5,X2_53)
% 2.38/1.02      | u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 2.38/1.02      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.38/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.38/1.02      | v2_struct_0(X0_53) = iProver_top
% 2.38/1.02      | v2_struct_0(X1_53) = iProver_top
% 2.38/1.02      | l1_pre_topc(X0_53) != iProver_top
% 2.38/1.02      | l1_pre_topc(X1_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X0_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X1_53) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1300]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3120,plain,
% 2.38/1.02      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK5,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK5,X1_53)
% 2.38/1.02      | u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.38/1.02      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.38/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.38/1.02      | v2_struct_0(X0_53) = iProver_top
% 2.38/1.02      | v2_struct_0(sK1) = iProver_top
% 2.38/1.02      | l1_pre_topc(X0_53) != iProver_top
% 2.38/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.38/1.02      | v2_pre_topc(X0_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(sK1) != iProver_top ),
% 2.38/1.02      inference(equality_resolution,[status(thm)],[c_2084]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3912,plain,
% 2.38/1.02      ( v2_pre_topc(X0_53) != iProver_top
% 2.38/1.02      | v2_struct_0(X0_53) = iProver_top
% 2.38/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.38/1.02      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.38/1.02      | u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.38/1.02      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK5,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK5,X1_53)
% 2.38/1.02      | l1_pre_topc(X0_53) != iProver_top ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_3120,c_36,c_37,c_38]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3913,plain,
% 2.38/1.02      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(sK1),sK5,u1_struct_0(X1_53)) = k2_tmap_1(X0_53,sK1,sK5,X1_53)
% 2.38/1.02      | u1_struct_0(X0_53) != u1_struct_0(sK4)
% 2.38/1.02      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.38/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 2.38/1.02      | v2_struct_0(X0_53) = iProver_top
% 2.38/1.02      | l1_pre_topc(X0_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X0_53) != iProver_top ),
% 2.38/1.02      inference(renaming,[status(thm)],[c_3912]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3923,plain,
% 2.38/1.02      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_53)) = k2_tmap_1(sK4,sK1,sK5,X0_53)
% 2.38/1.02      | m1_pre_topc(X0_53,sK4) != iProver_top
% 2.38/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 2.38/1.02      | v2_struct_0(sK4) = iProver_top
% 2.38/1.02      | l1_pre_topc(sK4) != iProver_top
% 2.38/1.02      | v2_pre_topc(sK4) != iProver_top ),
% 2.38/1.02      inference(equality_resolution,[status(thm)],[c_3913]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_45,plain,
% 2.38/1.02      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2573,plain,
% 2.38/1.02      ( ~ m1_pre_topc(sK4,X0_53)
% 2.38/1.02      | ~ l1_pre_topc(X0_53)
% 2.38/1.02      | l1_pre_topc(sK4) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_1327]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2690,plain,
% 2.38/1.02      ( ~ m1_pre_topc(sK4,sK2) | l1_pre_topc(sK4) | ~ l1_pre_topc(sK2) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_2573]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2691,plain,
% 2.38/1.02      ( m1_pre_topc(sK4,sK2) != iProver_top
% 2.38/1.02      | l1_pre_topc(sK4) = iProver_top
% 2.38/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_2690]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | v2_pre_topc(X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1328,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.38/1.02      | ~ l1_pre_topc(X1_53)
% 2.38/1.02      | ~ v2_pre_topc(X1_53)
% 2.38/1.02      | v2_pre_topc(X0_53) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2057,plain,
% 2.38/1.02      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.38/1.02      | l1_pre_topc(X1_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X1_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X0_53) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1328]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2829,plain,
% 2.38/1.02      ( l1_pre_topc(sK2) != iProver_top
% 2.38/1.02      | v2_pre_topc(sK4) = iProver_top
% 2.38/1.02      | v2_pre_topc(sK2) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_2072,c_2057]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4086,plain,
% 2.38/1.02      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_53)) = k2_tmap_1(sK4,sK1,sK5,X0_53)
% 2.38/1.02      | m1_pre_topc(X0_53,sK4) != iProver_top ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_3923,c_40,c_41,c_44,c_45,c_48,c_2691,c_2829]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4094,plain,
% 2.38/1.02      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_2068,c_4086]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4437,plain,
% 2.38/1.02      ( k3_tmap_1(X0_53,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
% 2.38/1.02      | m1_pre_topc(sK4,X0_53) != iProver_top
% 2.38/1.02      | v2_struct_0(X0_53) = iProver_top
% 2.38/1.02      | l1_pre_topc(X0_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(X0_53) != iProver_top ),
% 2.38/1.02      inference(light_normalisation,[status(thm)],[c_4436,c_4094]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4447,plain,
% 2.38/1.02      ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
% 2.38/1.02      | v2_struct_0(sK2) = iProver_top
% 2.38/1.02      | l1_pre_topc(sK2) != iProver_top
% 2.38/1.02      | v2_pre_topc(sK2) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_2072,c_4437]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4508,plain,
% 2.38/1.02      ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_4447,c_39,c_40,c_41]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_15,negated_conjecture,
% 2.38/1.02      ( ~ r1_tmap_1(sK4,sK1,sK5,sK6)
% 2.38/1.02      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
% 2.38/1.02      inference(cnf_transformation,[],[f86]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1321,negated_conjecture,
% 2.38/1.02      ( ~ r1_tmap_1(sK4,sK1,sK5,sK6)
% 2.38/1.02      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2064,plain,
% 2.38/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK6) != iProver_top
% 2.38/1.02      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1321]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_17,negated_conjecture,
% 2.38/1.02      ( sK6 = sK7 ),
% 2.38/1.02      inference(cnf_transformation,[],[f84]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1319,negated_conjecture,
% 2.38/1.02      ( sK6 = sK7 ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_17]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2149,plain,
% 2.38/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 2.38/1.02      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
% 2.38/1.02      inference(light_normalisation,[status(thm)],[c_2064,c_1319]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4512,plain,
% 2.38/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 2.38/1.02      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) != iProver_top ),
% 2.38/1.02      inference(demodulation,[status(thm)],[c_4508,c_2149]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_29,negated_conjecture,
% 2.38/1.02      ( ~ v2_struct_0(sK3) ),
% 2.38/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_42,plain,
% 2.38/1.02      ( v2_struct_0(sK3) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_51,plain,
% 2.38/1.02      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_18,negated_conjecture,
% 2.38/1.02      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.38/1.02      inference(cnf_transformation,[],[f83]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_53,plain,
% 2.38/1.02      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1333,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2397,plain,
% 2.38/1.02      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_1333]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3548,plain,
% 2.38/1.02      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_1333]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_13,plain,
% 2.38/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.38/1.02      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.38/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.38/1.02      | ~ v1_tsep_1(X4,X0)
% 2.38/1.02      | ~ m1_pre_topc(X4,X0)
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.38/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.38/1.02      | ~ v1_funct_1(X2)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | v2_struct_0(X4)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ l1_pre_topc(X0)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f89]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_11,plain,
% 2.38/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.38/1.02      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.38/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.38/1.02      | ~ m1_pre_topc(X4,X0)
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.38/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.38/1.02      | ~ v1_funct_1(X2)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | v2_struct_0(X4)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ l1_pre_topc(X0)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f87]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_179,plain,
% 2.38/1.02      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.38/1.02      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.38/1.02      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.38/1.02      | ~ m1_pre_topc(X4,X0)
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.38/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.38/1.02      | ~ v1_funct_1(X2)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | v2_struct_0(X4)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ l1_pre_topc(X0)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X0) ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_13,c_11]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_180,plain,
% 2.38/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.38/1.02      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.38/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.38/1.02      | ~ m1_pre_topc(X4,X0)
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.38/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.38/1.02      | ~ v1_funct_1(X2)
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X4)
% 2.38/1.02      | ~ l1_pre_topc(X0)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X0)
% 2.38/1.02      | ~ v2_pre_topc(X1) ),
% 2.38/1.02      inference(renaming,[status(thm)],[c_179]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_593,plain,
% 2.38/1.02      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.38/1.02      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.38/1.02      | ~ m1_pre_topc(X4,X0)
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.38/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.38/1.02      | ~ v1_funct_1(X2)
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X4)
% 2.38/1.02      | ~ l1_pre_topc(X0)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X0)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.38/1.02      | sK5 != X2 ),
% 2.38/1.02      inference(resolution_lifted,[status(thm)],[c_180,c_24]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_594,plain,
% 2.38/1.02      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.38/1.02      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.38/1.02      | ~ m1_pre_topc(X0,X2)
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.38/1.02      | ~ v1_funct_1(sK5)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(unflattening,[status(thm)],[c_593]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_598,plain,
% 2.38/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.38/1.02      | ~ m1_pre_topc(X0,X2)
% 2.38/1.02      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.38/1.02      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_594,c_25]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_599,plain,
% 2.38/1.02      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.38/1.02      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.38/1.02      | ~ m1_pre_topc(X0,X2)
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(renaming,[status(thm)],[c_598]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_5,plain,
% 2.38/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.38/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.38/1.02      | m1_subset_1(X2,u1_struct_0(X1))
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | ~ l1_pre_topc(X1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_634,plain,
% 2.38/1.02      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.38/1.02      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.38/1.02      | ~ m1_pre_topc(X0,X2)
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_599,c_5]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1303,plain,
% 2.38/1.02      ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,sK5,X0_53),X0_54)
% 2.38/1.02      | ~ r1_tmap_1(X2_53,X1_53,sK5,X0_54)
% 2.38/1.02      | ~ m1_pre_topc(X0_53,X2_53)
% 2.38/1.02      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 2.38/1.02      | v2_struct_0(X1_53)
% 2.38/1.02      | v2_struct_0(X2_53)
% 2.38/1.02      | v2_struct_0(X0_53)
% 2.38/1.02      | ~ l1_pre_topc(X1_53)
% 2.38/1.02      | ~ l1_pre_topc(X2_53)
% 2.38/1.02      | ~ v2_pre_topc(X1_53)
% 2.38/1.02      | ~ v2_pre_topc(X2_53)
% 2.38/1.02      | u1_struct_0(X2_53) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X1_53) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_634]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2662,plain,
% 2.38/1.02      ( r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK4,X1_53,sK5,X0_53),X0_54)
% 2.38/1.02      | ~ r1_tmap_1(sK4,X1_53,sK5,X0_54)
% 2.38/1.02      | ~ m1_pre_topc(X0_53,sK4)
% 2.38/1.02      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_53))))
% 2.38/1.02      | v2_struct_0(X1_53)
% 2.38/1.02      | v2_struct_0(X0_53)
% 2.38/1.02      | v2_struct_0(sK4)
% 2.38/1.02      | ~ l1_pre_topc(X1_53)
% 2.38/1.02      | ~ l1_pre_topc(sK4)
% 2.38/1.02      | ~ v2_pre_topc(X1_53)
% 2.38/1.02      | ~ v2_pre_topc(sK4)
% 2.38/1.02      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 2.38/1.02      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_1303]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3479,plain,
% 2.38/1.02      ( ~ r1_tmap_1(sK4,X0_53,sK5,X0_54)
% 2.38/1.02      | r1_tmap_1(sK3,X0_53,k2_tmap_1(sK4,X0_53,sK5,sK3),X0_54)
% 2.38/1.02      | ~ m1_pre_topc(sK3,sK4)
% 2.38/1.02      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53))))
% 2.38/1.02      | v2_struct_0(X0_53)
% 2.38/1.02      | v2_struct_0(sK4)
% 2.38/1.02      | v2_struct_0(sK3)
% 2.38/1.02      | ~ l1_pre_topc(X0_53)
% 2.38/1.02      | ~ l1_pre_topc(sK4)
% 2.38/1.02      | ~ v2_pre_topc(X0_53)
% 2.38/1.02      | ~ v2_pre_topc(sK4)
% 2.38/1.02      | u1_struct_0(X0_53) != u1_struct_0(sK1)
% 2.38/1.02      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_2662]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4095,plain,
% 2.38/1.02      ( ~ r1_tmap_1(sK4,X0_53,sK5,sK7)
% 2.38/1.02      | r1_tmap_1(sK3,X0_53,k2_tmap_1(sK4,X0_53,sK5,sK3),sK7)
% 2.38/1.02      | ~ m1_pre_topc(sK3,sK4)
% 2.38/1.02      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53))))
% 2.38/1.02      | v2_struct_0(X0_53)
% 2.38/1.02      | v2_struct_0(sK4)
% 2.38/1.02      | v2_struct_0(sK3)
% 2.38/1.02      | ~ l1_pre_topc(X0_53)
% 2.38/1.02      | ~ l1_pre_topc(sK4)
% 2.38/1.02      | ~ v2_pre_topc(X0_53)
% 2.38/1.02      | ~ v2_pre_topc(sK4)
% 2.38/1.02      | u1_struct_0(X0_53) != u1_struct_0(sK1)
% 2.38/1.02      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_3479]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4096,plain,
% 2.38/1.02      ( u1_struct_0(X0_53) != u1_struct_0(sK1)
% 2.38/1.02      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.38/1.02      | r1_tmap_1(sK4,X0_53,sK5,sK7) != iProver_top
% 2.38/1.02      | r1_tmap_1(sK3,X0_53,k2_tmap_1(sK4,X0_53,sK5,sK3),sK7) = iProver_top
% 2.38/1.02      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.38/1.02      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.38/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
% 2.38/1.02      | v2_struct_0(X0_53) = iProver_top
% 2.38/1.02      | v2_struct_0(sK4) = iProver_top
% 2.38/1.02      | v2_struct_0(sK3) = iProver_top
% 2.38/1.02      | l1_pre_topc(X0_53) != iProver_top
% 2.38/1.02      | l1_pre_topc(sK4) != iProver_top
% 2.38/1.02      | v2_pre_topc(X0_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(sK4) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_4095]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4098,plain,
% 2.38/1.02      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.38/1.02      | r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 2.38/1.02      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) = iProver_top
% 2.38/1.02      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.38/1.02      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.38/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 2.38/1.02      | v2_struct_0(sK4) = iProver_top
% 2.38/1.02      | v2_struct_0(sK1) = iProver_top
% 2.38/1.02      | v2_struct_0(sK3) = iProver_top
% 2.38/1.02      | l1_pre_topc(sK4) != iProver_top
% 2.38/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.38/1.02      | v2_pre_topc(sK4) != iProver_top
% 2.38/1.02      | v2_pre_topc(sK1) != iProver_top ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_4096]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4524,plain,
% 2.38/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_4512,c_36,c_37,c_38,c_40,c_41,c_42,c_44,c_45,c_48,
% 2.38/1.02                 c_51,c_53,c_2397,c_2691,c_2829,c_3548,c_4098]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_16,negated_conjecture,
% 2.38/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK6)
% 2.38/1.02      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
% 2.38/1.02      inference(cnf_transformation,[],[f85]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1320,negated_conjecture,
% 2.38/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK6)
% 2.38/1.02      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2065,plain,
% 2.38/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK6) = iProver_top
% 2.38/1.02      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1320]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2138,plain,
% 2.38/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 2.38/1.02      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
% 2.38/1.02      inference(light_normalisation,[status(thm)],[c_2065,c_1319]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4511,plain,
% 2.38/1.02      ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 2.38/1.02      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) = iProver_top ),
% 2.38/1.02      inference(demodulation,[status(thm)],[c_4508,c_2138]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_12,plain,
% 2.38/1.02      ( r1_tmap_1(X0,X1,X2,X3)
% 2.38/1.02      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.38/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.38/1.02      | ~ v1_tsep_1(X4,X0)
% 2.38/1.02      | ~ m1_pre_topc(X4,X0)
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.38/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.38/1.02      | ~ v1_funct_1(X2)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | v2_struct_0(X4)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ l1_pre_topc(X0)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f88]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_650,plain,
% 2.38/1.02      ( r1_tmap_1(X0,X1,X2,X3)
% 2.38/1.02      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.38/1.02      | ~ v1_tsep_1(X4,X0)
% 2.38/1.02      | ~ m1_pre_topc(X4,X0)
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.38/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.38/1.02      | ~ v1_funct_1(X2)
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X4)
% 2.38/1.02      | ~ l1_pre_topc(X0)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X0)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.38/1.02      | sK5 != X2 ),
% 2.38/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_651,plain,
% 2.38/1.02      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.38/1.02      | r1_tmap_1(X2,X1,sK5,X3)
% 2.38/1.02      | ~ v1_tsep_1(X0,X2)
% 2.38/1.02      | ~ m1_pre_topc(X0,X2)
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.38/1.02      | ~ v1_funct_1(sK5)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(unflattening,[status(thm)],[c_650]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_655,plain,
% 2.38/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.38/1.02      | ~ m1_pre_topc(X0,X2)
% 2.38/1.02      | ~ v1_tsep_1(X0,X2)
% 2.38/1.02      | r1_tmap_1(X2,X1,sK5,X3)
% 2.38/1.02      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_651,c_25]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_656,plain,
% 2.38/1.02      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.38/1.02      | r1_tmap_1(X2,X1,sK5,X3)
% 2.38/1.02      | ~ v1_tsep_1(X0,X2)
% 2.38/1.02      | ~ m1_pre_topc(X0,X2)
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(renaming,[status(thm)],[c_655]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_693,plain,
% 2.38/1.02      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.38/1.02      | r1_tmap_1(X2,X1,sK5,X3)
% 2.38/1.02      | ~ v1_tsep_1(X0,X2)
% 2.38/1.02      | ~ m1_pre_topc(X0,X2)
% 2.38/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.38/1.02      | v2_struct_0(X0)
% 2.38/1.02      | v2_struct_0(X1)
% 2.38/1.02      | v2_struct_0(X2)
% 2.38/1.02      | ~ l1_pre_topc(X1)
% 2.38/1.02      | ~ l1_pre_topc(X2)
% 2.38/1.02      | ~ v2_pre_topc(X1)
% 2.38/1.02      | ~ v2_pre_topc(X2)
% 2.38/1.02      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_656,c_5]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1302,plain,
% 2.38/1.02      ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(X2_53,X1_53,sK5,X0_53),X0_54)
% 2.38/1.02      | r1_tmap_1(X2_53,X1_53,sK5,X0_54)
% 2.38/1.02      | ~ v1_tsep_1(X0_53,X2_53)
% 2.38/1.02      | ~ m1_pre_topc(X0_53,X2_53)
% 2.38/1.02      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 2.38/1.02      | v2_struct_0(X1_53)
% 2.38/1.02      | v2_struct_0(X2_53)
% 2.38/1.02      | v2_struct_0(X0_53)
% 2.38/1.02      | ~ l1_pre_topc(X1_53)
% 2.38/1.02      | ~ l1_pre_topc(X2_53)
% 2.38/1.02      | ~ v2_pre_topc(X1_53)
% 2.38/1.02      | ~ v2_pre_topc(X2_53)
% 2.38/1.02      | u1_struct_0(X2_53) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(X1_53) != u1_struct_0(sK1) ),
% 2.38/1.02      inference(subtyping,[status(esa)],[c_693]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2661,plain,
% 2.38/1.02      ( ~ r1_tmap_1(X0_53,X1_53,k2_tmap_1(sK4,X1_53,sK5,X0_53),X0_54)
% 2.38/1.02      | r1_tmap_1(sK4,X1_53,sK5,X0_54)
% 2.38/1.02      | ~ v1_tsep_1(X0_53,sK4)
% 2.38/1.02      | ~ m1_pre_topc(X0_53,sK4)
% 2.38/1.02      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_53))))
% 2.38/1.02      | v2_struct_0(X1_53)
% 2.38/1.02      | v2_struct_0(X0_53)
% 2.38/1.02      | v2_struct_0(sK4)
% 2.38/1.02      | ~ l1_pre_topc(X1_53)
% 2.38/1.02      | ~ l1_pre_topc(sK4)
% 2.38/1.02      | ~ v2_pre_topc(X1_53)
% 2.38/1.02      | ~ v2_pre_topc(sK4)
% 2.38/1.02      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 2.38/1.02      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_1302]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3484,plain,
% 2.38/1.02      ( r1_tmap_1(sK4,X0_53,sK5,X0_54)
% 2.38/1.02      | ~ r1_tmap_1(sK3,X0_53,k2_tmap_1(sK4,X0_53,sK5,sK3),X0_54)
% 2.38/1.02      | ~ v1_tsep_1(sK3,sK4)
% 2.38/1.02      | ~ m1_pre_topc(sK3,sK4)
% 2.38/1.02      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53))))
% 2.38/1.02      | v2_struct_0(X0_53)
% 2.38/1.02      | v2_struct_0(sK4)
% 2.38/1.02      | v2_struct_0(sK3)
% 2.38/1.02      | ~ l1_pre_topc(X0_53)
% 2.38/1.02      | ~ l1_pre_topc(sK4)
% 2.38/1.02      | ~ v2_pre_topc(X0_53)
% 2.38/1.02      | ~ v2_pre_topc(sK4)
% 2.38/1.02      | u1_struct_0(X0_53) != u1_struct_0(sK1)
% 2.38/1.02      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_2661]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3713,plain,
% 2.38/1.02      ( r1_tmap_1(sK4,X0_53,sK5,sK7)
% 2.38/1.02      | ~ r1_tmap_1(sK3,X0_53,k2_tmap_1(sK4,X0_53,sK5,sK3),sK7)
% 2.38/1.02      | ~ v1_tsep_1(sK3,sK4)
% 2.38/1.02      | ~ m1_pre_topc(sK3,sK4)
% 2.38/1.02      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53))))
% 2.38/1.02      | v2_struct_0(X0_53)
% 2.38/1.02      | v2_struct_0(sK4)
% 2.38/1.02      | v2_struct_0(sK3)
% 2.38/1.02      | ~ l1_pre_topc(X0_53)
% 2.38/1.02      | ~ l1_pre_topc(sK4)
% 2.38/1.02      | ~ v2_pre_topc(X0_53)
% 2.38/1.02      | ~ v2_pre_topc(sK4)
% 2.38/1.02      | u1_struct_0(X0_53) != u1_struct_0(sK1)
% 2.38/1.02      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_3484]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3714,plain,
% 2.38/1.02      ( u1_struct_0(X0_53) != u1_struct_0(sK1)
% 2.38/1.02      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.38/1.02      | r1_tmap_1(sK4,X0_53,sK5,sK7) = iProver_top
% 2.38/1.02      | r1_tmap_1(sK3,X0_53,k2_tmap_1(sK4,X0_53,sK5,sK3),sK7) != iProver_top
% 2.38/1.02      | v1_tsep_1(sK3,sK4) != iProver_top
% 2.38/1.02      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.38/1.02      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.38/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_53)))) != iProver_top
% 2.38/1.02      | v2_struct_0(X0_53) = iProver_top
% 2.38/1.02      | v2_struct_0(sK4) = iProver_top
% 2.38/1.02      | v2_struct_0(sK3) = iProver_top
% 2.38/1.02      | l1_pre_topc(X0_53) != iProver_top
% 2.38/1.02      | l1_pre_topc(sK4) != iProver_top
% 2.38/1.02      | v2_pre_topc(X0_53) != iProver_top
% 2.38/1.02      | v2_pre_topc(sK4) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_3713]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3716,plain,
% 2.38/1.02      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.38/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.38/1.02      | r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 2.38/1.02      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) != iProver_top
% 2.38/1.02      | v1_tsep_1(sK3,sK4) != iProver_top
% 2.38/1.02      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.38/1.02      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.38/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 2.38/1.02      | v2_struct_0(sK4) = iProver_top
% 2.38/1.02      | v2_struct_0(sK1) = iProver_top
% 2.38/1.02      | v2_struct_0(sK3) = iProver_top
% 2.38/1.02      | l1_pre_topc(sK4) != iProver_top
% 2.38/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.38/1.02      | v2_pre_topc(sK4) != iProver_top
% 2.38/1.02      | v2_pre_topc(sK1) != iProver_top ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_3714]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_22,negated_conjecture,
% 2.38/1.02      ( v1_tsep_1(sK3,sK2) ),
% 2.38/1.02      inference(cnf_transformation,[],[f79]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_49,plain,
% 2.38/1.02      ( v1_tsep_1(sK3,sK2) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(contradiction,plain,
% 2.38/1.02      ( $false ),
% 2.38/1.02      inference(minisat,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_5106,c_4524,c_4511,c_3716,c_3548,c_2829,c_2691,c_2397,
% 2.38/1.02                 c_53,c_51,c_49,c_48,c_45,c_44,c_42,c_41,c_40,c_38,c_37,
% 2.38/1.02                 c_36]) ).
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.38/1.02  
% 2.38/1.02  ------                               Statistics
% 2.38/1.02  
% 2.38/1.02  ------ General
% 2.38/1.02  
% 2.38/1.02  abstr_ref_over_cycles:                  0
% 2.38/1.02  abstr_ref_under_cycles:                 0
% 2.38/1.02  gc_basic_clause_elim:                   0
% 2.38/1.02  forced_gc_time:                         0
% 2.38/1.02  parsing_time:                           0.011
% 2.38/1.02  unif_index_cands_time:                  0.
% 2.38/1.02  unif_index_add_time:                    0.
% 2.38/1.02  orderings_time:                         0.
% 2.38/1.02  out_proof_time:                         0.014
% 2.38/1.02  total_time:                             0.187
% 2.38/1.02  num_of_symbols:                         59
% 2.38/1.02  num_of_terms:                           2674
% 2.38/1.02  
% 2.38/1.02  ------ Preprocessing
% 2.38/1.02  
% 2.38/1.02  num_of_splits:                          0
% 2.38/1.02  num_of_split_atoms:                     0
% 2.38/1.02  num_of_reused_defs:                     0
% 2.38/1.02  num_eq_ax_congr_red:                    34
% 2.38/1.02  num_of_sem_filtered_clauses:            1
% 2.38/1.02  num_of_subtypes:                        3
% 2.38/1.02  monotx_restored_types:                  0
% 2.38/1.02  sat_num_of_epr_types:                   0
% 2.38/1.02  sat_num_of_non_cyclic_types:            0
% 2.38/1.02  sat_guarded_non_collapsed_types:        0
% 2.38/1.02  num_pure_diseq_elim:                    0
% 2.38/1.02  simp_replaced_by:                       0
% 2.38/1.02  res_preprocessed:                       156
% 2.38/1.02  prep_upred:                             0
% 2.38/1.02  prep_unflattend:                        21
% 2.38/1.02  smt_new_axioms:                         0
% 2.38/1.02  pred_elim_cands:                        9
% 2.38/1.02  pred_elim:                              2
% 2.38/1.02  pred_elim_cl:                           3
% 2.38/1.02  pred_elim_cycles:                       5
% 2.38/1.02  merged_defs:                            8
% 2.38/1.02  merged_defs_ncl:                        0
% 2.38/1.02  bin_hyper_res:                          8
% 2.38/1.02  prep_cycles:                            4
% 2.38/1.02  pred_elim_time:                         0.017
% 2.38/1.02  splitting_time:                         0.
% 2.38/1.02  sem_filter_time:                        0.
% 2.38/1.02  monotx_time:                            0.
% 2.38/1.02  subtype_inf_time:                       0.
% 2.38/1.02  
% 2.38/1.02  ------ Problem properties
% 2.38/1.02  
% 2.38/1.02  clauses:                                32
% 2.38/1.02  conjectures:                            18
% 2.38/1.02  epr:                                    16
% 2.38/1.02  horn:                                   23
% 2.38/1.02  ground:                                 18
% 2.38/1.02  unary:                                  16
% 2.38/1.02  binary:                                 4
% 2.38/1.02  lits:                                   118
% 2.38/1.02  lits_eq:                                11
% 2.38/1.02  fd_pure:                                0
% 2.38/1.02  fd_pseudo:                              0
% 2.38/1.02  fd_cond:                                0
% 2.38/1.02  fd_pseudo_cond:                         0
% 2.38/1.02  ac_symbols:                             0
% 2.38/1.02  
% 2.38/1.02  ------ Propositional Solver
% 2.38/1.02  
% 2.38/1.02  prop_solver_calls:                      32
% 2.38/1.02  prop_fast_solver_calls:                 1849
% 2.38/1.02  smt_solver_calls:                       0
% 2.38/1.02  smt_fast_solver_calls:                  0
% 2.38/1.02  prop_num_of_clauses:                    1165
% 2.38/1.02  prop_preprocess_simplified:             4848
% 2.38/1.02  prop_fo_subsumed:                       102
% 2.38/1.02  prop_solver_time:                       0.
% 2.38/1.02  smt_solver_time:                        0.
% 2.38/1.02  smt_fast_solver_time:                   0.
% 2.38/1.02  prop_fast_solver_time:                  0.
% 2.38/1.02  prop_unsat_core_time:                   0.
% 2.38/1.02  
% 2.38/1.02  ------ QBF
% 2.38/1.02  
% 2.38/1.02  qbf_q_res:                              0
% 2.38/1.02  qbf_num_tautologies:                    0
% 2.38/1.02  qbf_prep_cycles:                        0
% 2.38/1.02  
% 2.38/1.02  ------ BMC1
% 2.38/1.02  
% 2.38/1.02  bmc1_current_bound:                     -1
% 2.38/1.02  bmc1_last_solved_bound:                 -1
% 2.38/1.02  bmc1_unsat_core_size:                   -1
% 2.38/1.02  bmc1_unsat_core_parents_size:           -1
% 2.38/1.02  bmc1_merge_next_fun:                    0
% 2.38/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.38/1.02  
% 2.38/1.02  ------ Instantiation
% 2.38/1.02  
% 2.38/1.02  inst_num_of_clauses:                    359
% 2.38/1.02  inst_num_in_passive:                    33
% 2.38/1.02  inst_num_in_active:                     321
% 2.38/1.02  inst_num_in_unprocessed:                5
% 2.38/1.02  inst_num_of_loops:                      380
% 2.38/1.02  inst_num_of_learning_restarts:          0
% 2.38/1.02  inst_num_moves_active_passive:          49
% 2.38/1.02  inst_lit_activity:                      0
% 2.38/1.02  inst_lit_activity_moves:                0
% 2.38/1.02  inst_num_tautologies:                   0
% 2.38/1.02  inst_num_prop_implied:                  0
% 2.38/1.02  inst_num_existing_simplified:           0
% 2.38/1.02  inst_num_eq_res_simplified:             0
% 2.38/1.02  inst_num_child_elim:                    0
% 2.38/1.02  inst_num_of_dismatching_blockings:      79
% 2.38/1.02  inst_num_of_non_proper_insts:           483
% 2.38/1.02  inst_num_of_duplicates:                 0
% 2.38/1.02  inst_inst_num_from_inst_to_res:         0
% 2.38/1.02  inst_dismatching_checking_time:         0.
% 2.38/1.02  
% 2.38/1.02  ------ Resolution
% 2.38/1.02  
% 2.38/1.02  res_num_of_clauses:                     0
% 2.38/1.02  res_num_in_passive:                     0
% 2.38/1.02  res_num_in_active:                      0
% 2.38/1.02  res_num_of_loops:                       160
% 2.38/1.02  res_forward_subset_subsumed:            88
% 2.38/1.02  res_backward_subset_subsumed:           2
% 2.38/1.02  res_forward_subsumed:                   0
% 2.38/1.02  res_backward_subsumed:                  0
% 2.38/1.02  res_forward_subsumption_resolution:     3
% 2.38/1.02  res_backward_subsumption_resolution:    0
% 2.38/1.02  res_clause_to_clause_subsumption:       323
% 2.38/1.02  res_orphan_elimination:                 0
% 2.38/1.02  res_tautology_del:                      139
% 2.38/1.02  res_num_eq_res_simplified:              0
% 2.38/1.02  res_num_sel_changes:                    0
% 2.38/1.02  res_moves_from_active_to_pass:          0
% 2.38/1.02  
% 2.38/1.02  ------ Superposition
% 2.38/1.02  
% 2.38/1.02  sup_time_total:                         0.
% 2.38/1.02  sup_time_generating:                    0.
% 2.38/1.02  sup_time_sim_full:                      0.
% 2.38/1.02  sup_time_sim_immed:                     0.
% 2.38/1.02  
% 2.38/1.02  sup_num_of_clauses:                     76
% 2.38/1.02  sup_num_in_active:                      73
% 2.38/1.02  sup_num_in_passive:                     3
% 2.38/1.02  sup_num_of_loops:                       74
% 2.38/1.02  sup_fw_superposition:                   41
% 2.38/1.02  sup_bw_superposition:                   23
% 2.38/1.02  sup_immediate_simplified:               14
% 2.38/1.02  sup_given_eliminated:                   0
% 2.38/1.02  comparisons_done:                       0
% 2.38/1.02  comparisons_avoided:                    0
% 2.38/1.02  
% 2.38/1.02  ------ Simplifications
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  sim_fw_subset_subsumed:                 13
% 2.38/1.02  sim_bw_subset_subsumed:                 1
% 2.38/1.02  sim_fw_subsumed:                        0
% 2.38/1.02  sim_bw_subsumed:                        0
% 2.38/1.02  sim_fw_subsumption_res:                 2
% 2.38/1.02  sim_bw_subsumption_res:                 0
% 2.38/1.02  sim_tautology_del:                      7
% 2.38/1.02  sim_eq_tautology_del:                   0
% 2.38/1.02  sim_eq_res_simp:                        0
% 2.38/1.02  sim_fw_demodulated:                     0
% 2.38/1.02  sim_bw_demodulated:                     2
% 2.38/1.02  sim_light_normalised:                   4
% 2.38/1.02  sim_joinable_taut:                      0
% 2.38/1.02  sim_joinable_simp:                      0
% 2.38/1.02  sim_ac_normalised:                      0
% 2.38/1.02  sim_smt_subsumption:                    0
% 2.38/1.02  
%------------------------------------------------------------------------------
