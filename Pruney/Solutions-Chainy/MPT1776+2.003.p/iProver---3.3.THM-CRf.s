%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:20 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  228 (1411 expanded)
%              Number of clauses        :  139 ( 286 expanded)
%              Number of leaves         :   23 ( 577 expanded)
%              Depth                    :   27
%              Number of atoms          : 1733 (26628 expanded)
%              Number of equality atoms :  356 (2011 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal clause size      :   46 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f44,f51,f50,f49,f48,f47,f46,f45])).

fof(f80,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f63,plain,(
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

fof(f82,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f72,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f73,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f62,plain,(
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

fof(f75,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f76,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,
    ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
    | ~ r1_tmap_1(sK4,sK1,sK5,sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
    | r1_tmap_1(sK4,sK1,sK5,sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f42,plain,(
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

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f96,plain,(
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
    inference(equality_resolution,[],[f68])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f67,plain,(
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

fof(f94,plain,(
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
    inference(equality_resolution,[],[f67])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f95,plain,(
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
    inference(equality_resolution,[],[f69])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f64,plain,(
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

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1661,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2396,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1661])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1665,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2392,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1665])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f63])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_758,plain,
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
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_759,plain,
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
    inference(unflattening,[status(thm)],[c_758])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_763,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_759,c_28])).

cnf(c_764,plain,
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
    inference(renaming,[status(thm)],[c_763])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_795,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_764,c_17])).

cnf(c_1649,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X1_54,X2_54)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X3_54))))
    | v2_struct_0(X2_54)
    | v2_struct_0(X3_54)
    | ~ l1_pre_topc(X2_54)
    | ~ l1_pre_topc(X3_54)
    | ~ v2_pre_topc(X2_54)
    | ~ v2_pre_topc(X3_54)
    | k2_partfun1(u1_struct_0(X1_54),u1_struct_0(X3_54),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X2_54,X3_54,X1_54,X0_54,sK5)
    | u1_struct_0(X1_54) != u1_struct_0(sK4)
    | u1_struct_0(X3_54) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_795])).

cnf(c_2408,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK5,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,sK5)
    | u1_struct_0(X0_54) != u1_struct_0(sK4)
    | u1_struct_0(X1_54) != u1_struct_0(sK1)
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1649])).

cnf(c_4044,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK5,u1_struct_0(X1_54)) = k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK5)
    | u1_struct_0(X0_54) != u1_struct_0(sK4)
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2408])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_39,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4691,plain,
    ( v2_pre_topc(X2_54) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | u1_struct_0(X0_54) != u1_struct_0(sK4)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK5,u1_struct_0(X1_54)) = k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK5)
    | l1_pre_topc(X2_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4044,c_39,c_40,c_41])).

cnf(c_4692,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK5,u1_struct_0(X1_54)) = k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK5)
    | u1_struct_0(X0_54) != u1_struct_0(sK4)
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_4691])).

cnf(c_4703,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK4,X0_54,sK5)
    | m1_pre_topc(X0_54,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_54) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4692])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4932,plain,
    ( m1_pre_topc(sK4,X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK4) != iProver_top
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK4,X0_54,sK5)
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4703,c_51])).

cnf(c_4933,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK4,X0_54,sK5)
    | m1_pre_topc(X0_54,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_4932])).

cnf(c_4944,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(X0_54,sK1,sK4,sK3,sK5)
    | m1_pre_topc(sK4,X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_2392,c_4933])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f62])).

cnf(c_809,plain,
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
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_810,plain,
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
    inference(unflattening,[status(thm)],[c_809])).

cnf(c_814,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_810,c_28])).

cnf(c_815,plain,
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
    inference(renaming,[status(thm)],[c_814])).

cnf(c_1648,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X2_54))))
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | k2_partfun1(u1_struct_0(X1_54),u1_struct_0(X2_54),sK5,u1_struct_0(X0_54)) = k2_tmap_1(X1_54,X2_54,sK5,X0_54)
    | u1_struct_0(X1_54) != u1_struct_0(sK4)
    | u1_struct_0(X2_54) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_815])).

cnf(c_2409,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK5,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,sK5,X2_54)
    | u1_struct_0(X0_54) != u1_struct_0(sK4)
    | u1_struct_0(X1_54) != u1_struct_0(sK1)
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1648])).

cnf(c_3870,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK5,u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,sK5,X1_54)
    | u1_struct_0(X0_54) != u1_struct_0(sK4)
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2409])).

cnf(c_3961,plain,
    ( v2_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | u1_struct_0(X0_54) != u1_struct_0(sK4)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK5,u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,sK5,X1_54)
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3870,c_39,c_40,c_41])).

cnf(c_3962,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK5,u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,sK5,X1_54)
    | u1_struct_0(X0_54) != u1_struct_0(sK4)
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3961])).

cnf(c_3972,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK4,sK1,sK5,X0_54)
    | m1_pre_topc(X0_54,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3962])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_43,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_44,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_47,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_48,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1677,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | v2_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2381,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1677])).

cnf(c_2898,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2396,c_2381])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1676,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2937,plain,
    ( ~ m1_pre_topc(sK4,X0_54)
    | ~ l1_pre_topc(X0_54)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1676])).

cnf(c_3036,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2937])).

cnf(c_3037,plain,
    ( m1_pre_topc(sK4,sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3036])).

cnf(c_4594,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK4,sK1,sK5,X0_54)
    | m1_pre_topc(X0_54,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3972,c_43,c_44,c_47,c_48,c_51,c_2898,c_3037])).

cnf(c_4602,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_2392,c_4594])).

cnf(c_4945,plain,
    ( k3_tmap_1(X0_54,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
    | m1_pre_topc(sK4,X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4944,c_4602])).

cnf(c_4955,plain,
    ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2396,c_4945])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_42,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5030,plain,
    ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4955,c_42,c_43,c_44])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK6)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1670,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK6)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2388,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK6) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1670])).

cnf(c_20,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1668,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2466,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2388,c_1668])).

cnf(c_5034,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5030,c_2466])).

cnf(c_19,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK6)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1669,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK6)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2389,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK6) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1669])).

cnf(c_2455,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2389,c_1668])).

cnf(c_5033,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5030,c_2455])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f96])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f94])).

cnf(c_199,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_14])).

cnf(c_200,plain,
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
    inference(renaming,[status(thm)],[c_199])).

cnf(c_854,plain,
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
    inference(resolution_lifted,[status(thm)],[c_200,c_27])).

cnf(c_855,plain,
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
    inference(unflattening,[status(thm)],[c_854])).

cnf(c_859,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_855,c_28])).

cnf(c_860,plain,
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
    inference(renaming,[status(thm)],[c_859])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_895,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_860,c_8])).

cnf(c_1647,plain,
    ( r1_tmap_1(X0_54,X1_54,k2_tmap_1(X2_54,X1_54,sK5,X0_54),X0_55)
    | ~ r1_tmap_1(X2_54,X1_54,sK5,X0_55)
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | u1_struct_0(X2_54) != u1_struct_0(sK4)
    | u1_struct_0(X1_54) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_895])).

cnf(c_2727,plain,
    ( r1_tmap_1(X0_54,X1_54,k2_tmap_1(sK4,X1_54,sK5,X0_54),X0_55)
    | ~ r1_tmap_1(sK4,X1_54,sK5,X0_55)
    | ~ m1_pre_topc(X0_54,sK4)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_54))))
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X1_54) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1647])).

cnf(c_3450,plain,
    ( ~ r1_tmap_1(sK4,X0_54,sK5,X0_55)
    | r1_tmap_1(sK3,X0_54,k2_tmap_1(sK4,X0_54,sK5,sK3),X0_55)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2727])).

cnf(c_4444,plain,
    ( ~ r1_tmap_1(sK4,X0_54,sK5,sK7)
    | r1_tmap_1(sK3,X0_54,k2_tmap_1(sK4,X0_54,sK5,sK3),sK7)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3450])).

cnf(c_4445,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(sK4,X0_54,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,X0_54,k2_tmap_1(sK4,X0_54,sK5,sK3),sK7) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4444])).

cnf(c_4447,plain,
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
    inference(instantiation,[status(thm)],[c_4445])).

cnf(c_1679,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_3705,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1679])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f95])).

cnf(c_911,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_912,plain,
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
    inference(unflattening,[status(thm)],[c_911])).

cnf(c_916,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_912,c_28])).

cnf(c_917,plain,
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
    inference(renaming,[status(thm)],[c_916])).

cnf(c_954,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_917,c_8])).

cnf(c_1646,plain,
    ( ~ r1_tmap_1(X0_54,X1_54,k2_tmap_1(X2_54,X1_54,sK5,X0_54),X0_55)
    | r1_tmap_1(X2_54,X1_54,sK5,X0_55)
    | ~ v1_tsep_1(X0_54,X2_54)
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | u1_struct_0(X2_54) != u1_struct_0(sK4)
    | u1_struct_0(X1_54) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_954])).

cnf(c_2726,plain,
    ( ~ r1_tmap_1(X0_54,X1_54,k2_tmap_1(sK4,X1_54,sK5,X0_54),X0_55)
    | r1_tmap_1(sK4,X1_54,sK5,X0_55)
    | ~ v1_tsep_1(X0_54,sK4)
    | ~ m1_pre_topc(X0_54,sK4)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_54))))
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X1_54) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1646])).

cnf(c_3455,plain,
    ( r1_tmap_1(sK4,X0_54,sK5,X0_55)
    | ~ r1_tmap_1(sK3,X0_54,k2_tmap_1(sK4,X0_54,sK5,sK3),X0_55)
    | ~ v1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2726])).

cnf(c_3624,plain,
    ( r1_tmap_1(sK4,X0_54,sK5,sK7)
    | ~ r1_tmap_1(sK3,X0_54,k2_tmap_1(sK4,X0_54,sK5,sK3),sK7)
    | ~ v1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
    | v2_struct_0(X0_54)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3455])).

cnf(c_3625,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(sK4,X0_54,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,X0_54,k2_tmap_1(sK4,X0_54,sK5,sK3),sK7) != iProver_top
    | v1_tsep_1(sK3,sK4) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3624])).

cnf(c_3627,plain,
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
    inference(instantiation,[status(thm)],[c_3625])).

cnf(c_12,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1673,plain,
    ( ~ v1_tsep_1(X0_54,X1_54)
    | v1_tsep_1(X0_54,X2_54)
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | ~ r1_tarski(u1_struct_0(X0_54),u1_struct_0(X2_54))
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2810,plain,
    ( v1_tsep_1(sK3,X0_54)
    | ~ v1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(X0_54,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_54))
    | v2_struct_0(X0_54)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1673])).

cnf(c_3007,plain,
    ( v1_tsep_1(sK3,sK4)
    | ~ v1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2810])).

cnf(c_3008,plain,
    ( v1_tsep_1(sK3,sK4) = iProver_top
    | v1_tsep_1(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3007])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1128,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_1129,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_1128])).

cnf(c_1211,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_483,c_1129])).

cnf(c_1652,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | r1_tarski(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_1211])).

cnf(c_2825,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_2826,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2825])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1672,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54)))
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2740,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1672])).

cnf(c_2741,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2740])).

cnf(c_2725,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1679])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_56,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_54,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_25,negated_conjecture,
    ( v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_52,plain,
    ( v1_tsep_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_46,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_45,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5034,c_5033,c_4447,c_3705,c_3627,c_3037,c_3008,c_2898,c_2826,c_2741,c_2725,c_56,c_54,c_52,c_51,c_48,c_47,c_46,c_45,c_44,c_43,c_42,c_41,c_40,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.56/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.01  
% 2.56/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.56/1.01  
% 2.56/1.01  ------  iProver source info
% 2.56/1.01  
% 2.56/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.56/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.56/1.01  git: non_committed_changes: false
% 2.56/1.01  git: last_make_outside_of_git: false
% 2.56/1.01  
% 2.56/1.01  ------ 
% 2.56/1.01  
% 2.56/1.01  ------ Input Options
% 2.56/1.01  
% 2.56/1.01  --out_options                           all
% 2.56/1.01  --tptp_safe_out                         true
% 2.56/1.01  --problem_path                          ""
% 2.56/1.01  --include_path                          ""
% 2.56/1.01  --clausifier                            res/vclausify_rel
% 2.56/1.01  --clausifier_options                    --mode clausify
% 2.56/1.01  --stdin                                 false
% 2.56/1.01  --stats_out                             all
% 2.56/1.01  
% 2.56/1.01  ------ General Options
% 2.56/1.01  
% 2.56/1.01  --fof                                   false
% 2.56/1.01  --time_out_real                         305.
% 2.56/1.01  --time_out_virtual                      -1.
% 2.56/1.01  --symbol_type_check                     false
% 2.56/1.01  --clausify_out                          false
% 2.56/1.01  --sig_cnt_out                           false
% 2.56/1.01  --trig_cnt_out                          false
% 2.56/1.01  --trig_cnt_out_tolerance                1.
% 2.56/1.01  --trig_cnt_out_sk_spl                   false
% 2.56/1.01  --abstr_cl_out                          false
% 2.56/1.01  
% 2.56/1.01  ------ Global Options
% 2.56/1.01  
% 2.56/1.01  --schedule                              default
% 2.56/1.01  --add_important_lit                     false
% 2.56/1.01  --prop_solver_per_cl                    1000
% 2.56/1.01  --min_unsat_core                        false
% 2.56/1.01  --soft_assumptions                      false
% 2.56/1.01  --soft_lemma_size                       3
% 2.56/1.01  --prop_impl_unit_size                   0
% 2.56/1.01  --prop_impl_unit                        []
% 2.56/1.01  --share_sel_clauses                     true
% 2.56/1.01  --reset_solvers                         false
% 2.56/1.01  --bc_imp_inh                            [conj_cone]
% 2.56/1.01  --conj_cone_tolerance                   3.
% 2.56/1.01  --extra_neg_conj                        none
% 2.56/1.01  --large_theory_mode                     true
% 2.56/1.01  --prolific_symb_bound                   200
% 2.56/1.01  --lt_threshold                          2000
% 2.56/1.01  --clause_weak_htbl                      true
% 2.56/1.01  --gc_record_bc_elim                     false
% 2.56/1.01  
% 2.56/1.01  ------ Preprocessing Options
% 2.56/1.01  
% 2.56/1.01  --preprocessing_flag                    true
% 2.56/1.01  --time_out_prep_mult                    0.1
% 2.56/1.01  --splitting_mode                        input
% 2.56/1.01  --splitting_grd                         true
% 2.56/1.01  --splitting_cvd                         false
% 2.56/1.01  --splitting_cvd_svl                     false
% 2.56/1.01  --splitting_nvd                         32
% 2.56/1.01  --sub_typing                            true
% 2.56/1.01  --prep_gs_sim                           true
% 2.56/1.01  --prep_unflatten                        true
% 2.56/1.01  --prep_res_sim                          true
% 2.56/1.01  --prep_upred                            true
% 2.56/1.01  --prep_sem_filter                       exhaustive
% 2.56/1.01  --prep_sem_filter_out                   false
% 2.56/1.01  --pred_elim                             true
% 2.56/1.01  --res_sim_input                         true
% 2.56/1.01  --eq_ax_congr_red                       true
% 2.56/1.01  --pure_diseq_elim                       true
% 2.56/1.01  --brand_transform                       false
% 2.56/1.01  --non_eq_to_eq                          false
% 2.56/1.01  --prep_def_merge                        true
% 2.56/1.01  --prep_def_merge_prop_impl              false
% 2.56/1.01  --prep_def_merge_mbd                    true
% 2.56/1.01  --prep_def_merge_tr_red                 false
% 2.56/1.01  --prep_def_merge_tr_cl                  false
% 2.56/1.01  --smt_preprocessing                     true
% 2.56/1.01  --smt_ac_axioms                         fast
% 2.56/1.01  --preprocessed_out                      false
% 2.56/1.01  --preprocessed_stats                    false
% 2.56/1.01  
% 2.56/1.01  ------ Abstraction refinement Options
% 2.56/1.01  
% 2.56/1.01  --abstr_ref                             []
% 2.56/1.01  --abstr_ref_prep                        false
% 2.56/1.01  --abstr_ref_until_sat                   false
% 2.56/1.01  --abstr_ref_sig_restrict                funpre
% 2.56/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/1.01  --abstr_ref_under                       []
% 2.56/1.01  
% 2.56/1.01  ------ SAT Options
% 2.56/1.01  
% 2.56/1.01  --sat_mode                              false
% 2.56/1.01  --sat_fm_restart_options                ""
% 2.56/1.01  --sat_gr_def                            false
% 2.56/1.01  --sat_epr_types                         true
% 2.56/1.01  --sat_non_cyclic_types                  false
% 2.56/1.01  --sat_finite_models                     false
% 2.56/1.01  --sat_fm_lemmas                         false
% 2.56/1.01  --sat_fm_prep                           false
% 2.56/1.01  --sat_fm_uc_incr                        true
% 2.56/1.01  --sat_out_model                         small
% 2.56/1.01  --sat_out_clauses                       false
% 2.56/1.01  
% 2.56/1.01  ------ QBF Options
% 2.56/1.01  
% 2.56/1.01  --qbf_mode                              false
% 2.56/1.01  --qbf_elim_univ                         false
% 2.56/1.01  --qbf_dom_inst                          none
% 2.56/1.01  --qbf_dom_pre_inst                      false
% 2.56/1.01  --qbf_sk_in                             false
% 2.56/1.01  --qbf_pred_elim                         true
% 2.56/1.01  --qbf_split                             512
% 2.56/1.01  
% 2.56/1.01  ------ BMC1 Options
% 2.56/1.01  
% 2.56/1.01  --bmc1_incremental                      false
% 2.56/1.01  --bmc1_axioms                           reachable_all
% 2.56/1.01  --bmc1_min_bound                        0
% 2.56/1.01  --bmc1_max_bound                        -1
% 2.56/1.01  --bmc1_max_bound_default                -1
% 2.56/1.01  --bmc1_symbol_reachability              true
% 2.56/1.01  --bmc1_property_lemmas                  false
% 2.56/1.01  --bmc1_k_induction                      false
% 2.56/1.01  --bmc1_non_equiv_states                 false
% 2.56/1.01  --bmc1_deadlock                         false
% 2.56/1.01  --bmc1_ucm                              false
% 2.56/1.01  --bmc1_add_unsat_core                   none
% 2.56/1.01  --bmc1_unsat_core_children              false
% 2.56/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/1.01  --bmc1_out_stat                         full
% 2.56/1.01  --bmc1_ground_init                      false
% 2.56/1.01  --bmc1_pre_inst_next_state              false
% 2.56/1.01  --bmc1_pre_inst_state                   false
% 2.56/1.01  --bmc1_pre_inst_reach_state             false
% 2.56/1.01  --bmc1_out_unsat_core                   false
% 2.56/1.01  --bmc1_aig_witness_out                  false
% 2.56/1.01  --bmc1_verbose                          false
% 2.56/1.01  --bmc1_dump_clauses_tptp                false
% 2.56/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.56/1.01  --bmc1_dump_file                        -
% 2.56/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.56/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.56/1.01  --bmc1_ucm_extend_mode                  1
% 2.56/1.01  --bmc1_ucm_init_mode                    2
% 2.56/1.01  --bmc1_ucm_cone_mode                    none
% 2.56/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.56/1.01  --bmc1_ucm_relax_model                  4
% 2.56/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.56/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/1.01  --bmc1_ucm_layered_model                none
% 2.56/1.01  --bmc1_ucm_max_lemma_size               10
% 2.56/1.01  
% 2.56/1.01  ------ AIG Options
% 2.56/1.01  
% 2.56/1.01  --aig_mode                              false
% 2.56/1.01  
% 2.56/1.01  ------ Instantiation Options
% 2.56/1.01  
% 2.56/1.01  --instantiation_flag                    true
% 2.56/1.01  --inst_sos_flag                         false
% 2.56/1.01  --inst_sos_phase                        true
% 2.56/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/1.01  --inst_lit_sel_side                     num_symb
% 2.56/1.01  --inst_solver_per_active                1400
% 2.56/1.01  --inst_solver_calls_frac                1.
% 2.56/1.01  --inst_passive_queue_type               priority_queues
% 2.56/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/1.01  --inst_passive_queues_freq              [25;2]
% 2.56/1.01  --inst_dismatching                      true
% 2.56/1.01  --inst_eager_unprocessed_to_passive     true
% 2.56/1.01  --inst_prop_sim_given                   true
% 2.56/1.01  --inst_prop_sim_new                     false
% 2.56/1.01  --inst_subs_new                         false
% 2.56/1.01  --inst_eq_res_simp                      false
% 2.56/1.01  --inst_subs_given                       false
% 2.56/1.01  --inst_orphan_elimination               true
% 2.56/1.01  --inst_learning_loop_flag               true
% 2.56/1.01  --inst_learning_start                   3000
% 2.56/1.01  --inst_learning_factor                  2
% 2.56/1.01  --inst_start_prop_sim_after_learn       3
% 2.56/1.01  --inst_sel_renew                        solver
% 2.56/1.01  --inst_lit_activity_flag                true
% 2.56/1.01  --inst_restr_to_given                   false
% 2.56/1.01  --inst_activity_threshold               500
% 2.56/1.01  --inst_out_proof                        true
% 2.56/1.01  
% 2.56/1.01  ------ Resolution Options
% 2.56/1.01  
% 2.56/1.01  --resolution_flag                       true
% 2.56/1.01  --res_lit_sel                           adaptive
% 2.56/1.01  --res_lit_sel_side                      none
% 2.56/1.01  --res_ordering                          kbo
% 2.56/1.01  --res_to_prop_solver                    active
% 2.56/1.01  --res_prop_simpl_new                    false
% 2.56/1.01  --res_prop_simpl_given                  true
% 2.56/1.01  --res_passive_queue_type                priority_queues
% 2.56/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/1.01  --res_passive_queues_freq               [15;5]
% 2.56/1.01  --res_forward_subs                      full
% 2.56/1.01  --res_backward_subs                     full
% 2.56/1.01  --res_forward_subs_resolution           true
% 2.56/1.01  --res_backward_subs_resolution          true
% 2.56/1.01  --res_orphan_elimination                true
% 2.56/1.01  --res_time_limit                        2.
% 2.56/1.01  --res_out_proof                         true
% 2.56/1.01  
% 2.56/1.01  ------ Superposition Options
% 2.56/1.01  
% 2.56/1.01  --superposition_flag                    true
% 2.56/1.01  --sup_passive_queue_type                priority_queues
% 2.56/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.56/1.01  --demod_completeness_check              fast
% 2.56/1.01  --demod_use_ground                      true
% 2.56/1.01  --sup_to_prop_solver                    passive
% 2.56/1.01  --sup_prop_simpl_new                    true
% 2.56/1.01  --sup_prop_simpl_given                  true
% 2.56/1.01  --sup_fun_splitting                     false
% 2.56/1.01  --sup_smt_interval                      50000
% 2.56/1.01  
% 2.56/1.01  ------ Superposition Simplification Setup
% 2.56/1.01  
% 2.56/1.01  --sup_indices_passive                   []
% 2.56/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.01  --sup_full_bw                           [BwDemod]
% 2.56/1.01  --sup_immed_triv                        [TrivRules]
% 2.56/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.01  --sup_immed_bw_main                     []
% 2.56/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.01  
% 2.56/1.01  ------ Combination Options
% 2.56/1.01  
% 2.56/1.01  --comb_res_mult                         3
% 2.56/1.01  --comb_sup_mult                         2
% 2.56/1.01  --comb_inst_mult                        10
% 2.56/1.01  
% 2.56/1.01  ------ Debug Options
% 2.56/1.01  
% 2.56/1.01  --dbg_backtrace                         false
% 2.56/1.01  --dbg_dump_prop_clauses                 false
% 2.56/1.01  --dbg_dump_prop_clauses_file            -
% 2.56/1.01  --dbg_out_stat                          false
% 2.56/1.01  ------ Parsing...
% 2.56/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.56/1.01  
% 2.56/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.56/1.01  
% 2.56/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.56/1.01  
% 2.56/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.56/1.01  ------ Proving...
% 2.56/1.01  ------ Problem Properties 
% 2.56/1.01  
% 2.56/1.01  
% 2.56/1.01  clauses                                 32
% 2.56/1.01  conjectures                             18
% 2.56/1.01  EPR                                     16
% 2.56/1.01  Horn                                    23
% 2.56/1.01  unary                                   16
% 2.56/1.01  binary                                  3
% 2.56/1.01  lits                                    119
% 2.56/1.01  lits eq                                 13
% 2.56/1.01  fd_pure                                 0
% 2.56/1.01  fd_pseudo                               0
% 2.56/1.01  fd_cond                                 0
% 2.56/1.01  fd_pseudo_cond                          0
% 2.56/1.01  AC symbols                              0
% 2.56/1.01  
% 2.56/1.01  ------ Schedule dynamic 5 is on 
% 2.56/1.01  
% 2.56/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.56/1.01  
% 2.56/1.01  
% 2.56/1.01  ------ 
% 2.56/1.01  Current options:
% 2.56/1.01  ------ 
% 2.56/1.01  
% 2.56/1.01  ------ Input Options
% 2.56/1.01  
% 2.56/1.01  --out_options                           all
% 2.56/1.01  --tptp_safe_out                         true
% 2.56/1.01  --problem_path                          ""
% 2.56/1.01  --include_path                          ""
% 2.56/1.01  --clausifier                            res/vclausify_rel
% 2.56/1.01  --clausifier_options                    --mode clausify
% 2.56/1.01  --stdin                                 false
% 2.56/1.01  --stats_out                             all
% 2.56/1.01  
% 2.56/1.01  ------ General Options
% 2.56/1.01  
% 2.56/1.01  --fof                                   false
% 2.56/1.01  --time_out_real                         305.
% 2.56/1.01  --time_out_virtual                      -1.
% 2.56/1.01  --symbol_type_check                     false
% 2.56/1.01  --clausify_out                          false
% 2.56/1.01  --sig_cnt_out                           false
% 2.56/1.01  --trig_cnt_out                          false
% 2.56/1.01  --trig_cnt_out_tolerance                1.
% 2.56/1.01  --trig_cnt_out_sk_spl                   false
% 2.56/1.01  --abstr_cl_out                          false
% 2.56/1.01  
% 2.56/1.01  ------ Global Options
% 2.56/1.01  
% 2.56/1.01  --schedule                              default
% 2.56/1.01  --add_important_lit                     false
% 2.56/1.01  --prop_solver_per_cl                    1000
% 2.56/1.01  --min_unsat_core                        false
% 2.56/1.01  --soft_assumptions                      false
% 2.56/1.01  --soft_lemma_size                       3
% 2.56/1.01  --prop_impl_unit_size                   0
% 2.56/1.01  --prop_impl_unit                        []
% 2.56/1.01  --share_sel_clauses                     true
% 2.56/1.01  --reset_solvers                         false
% 2.56/1.01  --bc_imp_inh                            [conj_cone]
% 2.56/1.01  --conj_cone_tolerance                   3.
% 2.56/1.01  --extra_neg_conj                        none
% 2.56/1.01  --large_theory_mode                     true
% 2.56/1.01  --prolific_symb_bound                   200
% 2.56/1.01  --lt_threshold                          2000
% 2.56/1.01  --clause_weak_htbl                      true
% 2.56/1.01  --gc_record_bc_elim                     false
% 2.56/1.01  
% 2.56/1.01  ------ Preprocessing Options
% 2.56/1.01  
% 2.56/1.01  --preprocessing_flag                    true
% 2.56/1.01  --time_out_prep_mult                    0.1
% 2.56/1.01  --splitting_mode                        input
% 2.56/1.01  --splitting_grd                         true
% 2.56/1.01  --splitting_cvd                         false
% 2.56/1.01  --splitting_cvd_svl                     false
% 2.56/1.01  --splitting_nvd                         32
% 2.56/1.01  --sub_typing                            true
% 2.56/1.01  --prep_gs_sim                           true
% 2.56/1.01  --prep_unflatten                        true
% 2.56/1.01  --prep_res_sim                          true
% 2.56/1.01  --prep_upred                            true
% 2.56/1.01  --prep_sem_filter                       exhaustive
% 2.56/1.01  --prep_sem_filter_out                   false
% 2.56/1.01  --pred_elim                             true
% 2.56/1.01  --res_sim_input                         true
% 2.56/1.01  --eq_ax_congr_red                       true
% 2.56/1.01  --pure_diseq_elim                       true
% 2.56/1.01  --brand_transform                       false
% 2.56/1.01  --non_eq_to_eq                          false
% 2.56/1.01  --prep_def_merge                        true
% 2.56/1.01  --prep_def_merge_prop_impl              false
% 2.56/1.01  --prep_def_merge_mbd                    true
% 2.56/1.01  --prep_def_merge_tr_red                 false
% 2.56/1.01  --prep_def_merge_tr_cl                  false
% 2.56/1.01  --smt_preprocessing                     true
% 2.56/1.01  --smt_ac_axioms                         fast
% 2.56/1.01  --preprocessed_out                      false
% 2.56/1.01  --preprocessed_stats                    false
% 2.56/1.01  
% 2.56/1.01  ------ Abstraction refinement Options
% 2.56/1.01  
% 2.56/1.01  --abstr_ref                             []
% 2.56/1.01  --abstr_ref_prep                        false
% 2.56/1.01  --abstr_ref_until_sat                   false
% 2.56/1.01  --abstr_ref_sig_restrict                funpre
% 2.56/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/1.01  --abstr_ref_under                       []
% 2.56/1.01  
% 2.56/1.01  ------ SAT Options
% 2.56/1.01  
% 2.56/1.01  --sat_mode                              false
% 2.56/1.01  --sat_fm_restart_options                ""
% 2.56/1.01  --sat_gr_def                            false
% 2.56/1.01  --sat_epr_types                         true
% 2.56/1.01  --sat_non_cyclic_types                  false
% 2.56/1.01  --sat_finite_models                     false
% 2.56/1.01  --sat_fm_lemmas                         false
% 2.56/1.01  --sat_fm_prep                           false
% 2.56/1.01  --sat_fm_uc_incr                        true
% 2.56/1.01  --sat_out_model                         small
% 2.56/1.01  --sat_out_clauses                       false
% 2.56/1.01  
% 2.56/1.01  ------ QBF Options
% 2.56/1.01  
% 2.56/1.01  --qbf_mode                              false
% 2.56/1.01  --qbf_elim_univ                         false
% 2.56/1.01  --qbf_dom_inst                          none
% 2.56/1.01  --qbf_dom_pre_inst                      false
% 2.56/1.01  --qbf_sk_in                             false
% 2.56/1.01  --qbf_pred_elim                         true
% 2.56/1.01  --qbf_split                             512
% 2.56/1.01  
% 2.56/1.01  ------ BMC1 Options
% 2.56/1.01  
% 2.56/1.01  --bmc1_incremental                      false
% 2.56/1.01  --bmc1_axioms                           reachable_all
% 2.56/1.01  --bmc1_min_bound                        0
% 2.56/1.01  --bmc1_max_bound                        -1
% 2.56/1.01  --bmc1_max_bound_default                -1
% 2.56/1.01  --bmc1_symbol_reachability              true
% 2.56/1.01  --bmc1_property_lemmas                  false
% 2.56/1.01  --bmc1_k_induction                      false
% 2.56/1.01  --bmc1_non_equiv_states                 false
% 2.56/1.01  --bmc1_deadlock                         false
% 2.56/1.01  --bmc1_ucm                              false
% 2.56/1.01  --bmc1_add_unsat_core                   none
% 2.56/1.01  --bmc1_unsat_core_children              false
% 2.56/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/1.01  --bmc1_out_stat                         full
% 2.56/1.01  --bmc1_ground_init                      false
% 2.56/1.01  --bmc1_pre_inst_next_state              false
% 2.56/1.01  --bmc1_pre_inst_state                   false
% 2.56/1.01  --bmc1_pre_inst_reach_state             false
% 2.56/1.01  --bmc1_out_unsat_core                   false
% 2.56/1.01  --bmc1_aig_witness_out                  false
% 2.56/1.01  --bmc1_verbose                          false
% 2.56/1.01  --bmc1_dump_clauses_tptp                false
% 2.56/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.56/1.01  --bmc1_dump_file                        -
% 2.56/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.56/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.56/1.01  --bmc1_ucm_extend_mode                  1
% 2.56/1.01  --bmc1_ucm_init_mode                    2
% 2.56/1.01  --bmc1_ucm_cone_mode                    none
% 2.56/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.56/1.01  --bmc1_ucm_relax_model                  4
% 2.56/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.56/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/1.01  --bmc1_ucm_layered_model                none
% 2.56/1.01  --bmc1_ucm_max_lemma_size               10
% 2.56/1.01  
% 2.56/1.01  ------ AIG Options
% 2.56/1.01  
% 2.56/1.01  --aig_mode                              false
% 2.56/1.01  
% 2.56/1.01  ------ Instantiation Options
% 2.56/1.01  
% 2.56/1.01  --instantiation_flag                    true
% 2.56/1.01  --inst_sos_flag                         false
% 2.56/1.01  --inst_sos_phase                        true
% 2.56/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/1.01  --inst_lit_sel_side                     none
% 2.56/1.01  --inst_solver_per_active                1400
% 2.56/1.01  --inst_solver_calls_frac                1.
% 2.56/1.01  --inst_passive_queue_type               priority_queues
% 2.56/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/1.01  --inst_passive_queues_freq              [25;2]
% 2.56/1.01  --inst_dismatching                      true
% 2.56/1.01  --inst_eager_unprocessed_to_passive     true
% 2.56/1.01  --inst_prop_sim_given                   true
% 2.56/1.01  --inst_prop_sim_new                     false
% 2.56/1.01  --inst_subs_new                         false
% 2.56/1.01  --inst_eq_res_simp                      false
% 2.56/1.01  --inst_subs_given                       false
% 2.56/1.01  --inst_orphan_elimination               true
% 2.56/1.01  --inst_learning_loop_flag               true
% 2.56/1.01  --inst_learning_start                   3000
% 2.56/1.01  --inst_learning_factor                  2
% 2.56/1.01  --inst_start_prop_sim_after_learn       3
% 2.56/1.01  --inst_sel_renew                        solver
% 2.56/1.01  --inst_lit_activity_flag                true
% 2.56/1.01  --inst_restr_to_given                   false
% 2.56/1.01  --inst_activity_threshold               500
% 2.56/1.01  --inst_out_proof                        true
% 2.56/1.01  
% 2.56/1.01  ------ Resolution Options
% 2.56/1.01  
% 2.56/1.01  --resolution_flag                       false
% 2.56/1.01  --res_lit_sel                           adaptive
% 2.56/1.01  --res_lit_sel_side                      none
% 2.56/1.01  --res_ordering                          kbo
% 2.56/1.01  --res_to_prop_solver                    active
% 2.56/1.01  --res_prop_simpl_new                    false
% 2.56/1.01  --res_prop_simpl_given                  true
% 2.56/1.01  --res_passive_queue_type                priority_queues
% 2.56/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/1.01  --res_passive_queues_freq               [15;5]
% 2.56/1.01  --res_forward_subs                      full
% 2.56/1.01  --res_backward_subs                     full
% 2.56/1.01  --res_forward_subs_resolution           true
% 2.56/1.01  --res_backward_subs_resolution          true
% 2.56/1.01  --res_orphan_elimination                true
% 2.56/1.01  --res_time_limit                        2.
% 2.56/1.01  --res_out_proof                         true
% 2.56/1.01  
% 2.56/1.01  ------ Superposition Options
% 2.56/1.01  
% 2.56/1.01  --superposition_flag                    true
% 2.56/1.01  --sup_passive_queue_type                priority_queues
% 2.56/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.56/1.01  --demod_completeness_check              fast
% 2.56/1.01  --demod_use_ground                      true
% 2.56/1.01  --sup_to_prop_solver                    passive
% 2.56/1.01  --sup_prop_simpl_new                    true
% 2.56/1.01  --sup_prop_simpl_given                  true
% 2.56/1.01  --sup_fun_splitting                     false
% 2.56/1.01  --sup_smt_interval                      50000
% 2.56/1.01  
% 2.56/1.01  ------ Superposition Simplification Setup
% 2.56/1.01  
% 2.56/1.01  --sup_indices_passive                   []
% 2.56/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.01  --sup_full_bw                           [BwDemod]
% 2.56/1.01  --sup_immed_triv                        [TrivRules]
% 2.56/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.01  --sup_immed_bw_main                     []
% 2.56/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.01  
% 2.56/1.01  ------ Combination Options
% 2.56/1.01  
% 2.56/1.01  --comb_res_mult                         3
% 2.56/1.01  --comb_sup_mult                         2
% 2.56/1.01  --comb_inst_mult                        10
% 2.56/1.01  
% 2.56/1.01  ------ Debug Options
% 2.56/1.01  
% 2.56/1.01  --dbg_backtrace                         false
% 2.56/1.01  --dbg_dump_prop_clauses                 false
% 2.56/1.01  --dbg_dump_prop_clauses_file            -
% 2.56/1.01  --dbg_out_stat                          false
% 2.56/1.01  
% 2.56/1.01  
% 2.56/1.01  
% 2.56/1.01  
% 2.56/1.01  ------ Proving...
% 2.56/1.01  
% 2.56/1.01  
% 2.56/1.01  % SZS status Theorem for theBenchmark.p
% 2.56/1.01  
% 2.56/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.56/1.01  
% 2.56/1.01  fof(f14,conjecture,(
% 2.56/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 2.56/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.01  
% 2.56/1.01  fof(f15,negated_conjecture,(
% 2.56/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 2.56/1.01    inference(negated_conjecture,[],[f14])).
% 2.56/1.01  
% 2.56/1.01  fof(f36,plain,(
% 2.56/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.56/1.01    inference(ennf_transformation,[],[f15])).
% 2.56/1.01  
% 2.56/1.01  fof(f37,plain,(
% 2.56/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.56/1.01    inference(flattening,[],[f36])).
% 2.56/1.01  
% 2.56/1.01  fof(f43,plain,(
% 2.56/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.56/1.01    inference(nnf_transformation,[],[f37])).
% 2.56/1.01  
% 2.56/1.01  fof(f44,plain,(
% 2.56/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.56/1.01    inference(flattening,[],[f43])).
% 2.56/1.01  
% 2.56/1.01  fof(f51,plain,(
% 2.56/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | r1_tmap_1(X3,X0,X4,X5)) & sK7 = X5 & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.56/1.01    introduced(choice_axiom,[])).
% 2.56/1.01  
% 2.56/1.01  fof(f50,plain,(
% 2.56/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,sK6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,sK6)) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.56/1.01    introduced(choice_axiom,[])).
% 2.56/1.01  
% 2.56/1.01  fof(f49,plain,(
% 2.56/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X6) | ~r1_tmap_1(X3,X0,sK5,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X6) | r1_tmap_1(X3,X0,sK5,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 2.56/1.01    introduced(choice_axiom,[])).
% 2.56/1.01  
% 2.56/1.01  fof(f48,plain,(
% 2.56/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X6) | ~r1_tmap_1(sK4,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X6) | r1_tmap_1(sK4,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_pre_topc(X2,sK4) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X1) & ~v2_struct_0(sK4))) )),
% 2.56/1.01    introduced(choice_axiom,[])).
% 2.56/1.01  
% 2.56/1.01  fof(f47,plain,(
% 2.56/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK3,X3) & m1_pre_topc(sK3,X1) & v1_tsep_1(sK3,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 2.56/1.01    introduced(choice_axiom,[])).
% 2.56/1.01  
% 2.56/1.01  fof(f46,plain,(
% 2.56/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK2) & v1_tsep_1(X2,sK2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.56/1.01    introduced(choice_axiom,[])).
% 2.56/1.01  
% 2.56/1.01  fof(f45,plain,(
% 2.56/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.56/1.01    introduced(choice_axiom,[])).
% 2.56/1.01  
% 2.56/1.01  fof(f52,plain,(
% 2.56/1.01    (((((((~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | ~r1_tmap_1(sK4,sK1,sK5,sK6)) & (r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | r1_tmap_1(sK4,sK1,sK5,sK6)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK3,sK2) & v1_tsep_1(sK3,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.56/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f44,f51,f50,f49,f48,f47,f46,f45])).
% 2.56/1.01  
% 2.56/1.01  fof(f80,plain,(
% 2.56/1.01    m1_pre_topc(sK4,sK2)),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f86,plain,(
% 2.56/1.01    m1_pre_topc(sK3,sK4)),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f8,axiom,(
% 2.56/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.56/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.01  
% 2.56/1.01  fof(f25,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.56/1.01    inference(ennf_transformation,[],[f8])).
% 2.56/1.01  
% 2.56/1.01  fof(f26,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.56/1.01    inference(flattening,[],[f25])).
% 2.56/1.01  
% 2.56/1.01  fof(f63,plain,(
% 2.56/1.01    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.56/1.01    inference(cnf_transformation,[],[f26])).
% 2.56/1.01  
% 2.56/1.01  fof(f82,plain,(
% 2.56/1.01    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f81,plain,(
% 2.56/1.01    v1_funct_1(sK5)),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f13,axiom,(
% 2.56/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.56/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.01  
% 2.56/1.01  fof(f34,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.56/1.01    inference(ennf_transformation,[],[f13])).
% 2.56/1.01  
% 2.56/1.01  fof(f35,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.56/1.01    inference(flattening,[],[f34])).
% 2.56/1.01  
% 2.56/1.01  fof(f70,plain,(
% 2.56/1.01    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.56/1.01    inference(cnf_transformation,[],[f35])).
% 2.56/1.01  
% 2.56/1.01  fof(f71,plain,(
% 2.56/1.01    ~v2_struct_0(sK1)),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f72,plain,(
% 2.56/1.01    v2_pre_topc(sK1)),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f73,plain,(
% 2.56/1.01    l1_pre_topc(sK1)),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f83,plain,(
% 2.56/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f7,axiom,(
% 2.56/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.56/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.01  
% 2.56/1.01  fof(f23,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.56/1.01    inference(ennf_transformation,[],[f7])).
% 2.56/1.01  
% 2.56/1.01  fof(f24,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.56/1.01    inference(flattening,[],[f23])).
% 2.56/1.01  
% 2.56/1.01  fof(f62,plain,(
% 2.56/1.01    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.56/1.01    inference(cnf_transformation,[],[f24])).
% 2.56/1.01  
% 2.56/1.01  fof(f75,plain,(
% 2.56/1.01    v2_pre_topc(sK2)),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f76,plain,(
% 2.56/1.01    l1_pre_topc(sK2)),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f79,plain,(
% 2.56/1.01    ~v2_struct_0(sK4)),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f4,axiom,(
% 2.56/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.56/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.01  
% 2.56/1.01  fof(f18,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.56/1.01    inference(ennf_transformation,[],[f4])).
% 2.56/1.01  
% 2.56/1.01  fof(f19,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.56/1.01    inference(flattening,[],[f18])).
% 2.56/1.01  
% 2.56/1.01  fof(f59,plain,(
% 2.56/1.01    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.56/1.01    inference(cnf_transformation,[],[f19])).
% 2.56/1.01  
% 2.56/1.01  fof(f5,axiom,(
% 2.56/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.56/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.01  
% 2.56/1.01  fof(f20,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.56/1.01    inference(ennf_transformation,[],[f5])).
% 2.56/1.01  
% 2.56/1.01  fof(f60,plain,(
% 2.56/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.56/1.01    inference(cnf_transformation,[],[f20])).
% 2.56/1.01  
% 2.56/1.01  fof(f74,plain,(
% 2.56/1.01    ~v2_struct_0(sK2)),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f91,plain,(
% 2.56/1.01    ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | ~r1_tmap_1(sK4,sK1,sK5,sK6)),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f89,plain,(
% 2.56/1.01    sK6 = sK7),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f90,plain,(
% 2.56/1.01    r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | r1_tmap_1(sK4,sK1,sK5,sK6)),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f12,axiom,(
% 2.56/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.56/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.01  
% 2.56/1.01  fof(f32,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.56/1.01    inference(ennf_transformation,[],[f12])).
% 2.56/1.01  
% 2.56/1.01  fof(f33,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.56/1.01    inference(flattening,[],[f32])).
% 2.56/1.01  
% 2.56/1.01  fof(f42,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4))) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.56/1.01    inference(nnf_transformation,[],[f33])).
% 2.56/1.01  
% 2.56/1.01  fof(f68,plain,(
% 2.56/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.56/1.01    inference(cnf_transformation,[],[f42])).
% 2.56/1.01  
% 2.56/1.01  fof(f96,plain,(
% 2.56/1.01    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.56/1.01    inference(equality_resolution,[],[f68])).
% 2.56/1.01  
% 2.56/1.01  fof(f11,axiom,(
% 2.56/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.56/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.01  
% 2.56/1.01  fof(f30,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.56/1.01    inference(ennf_transformation,[],[f11])).
% 2.56/1.01  
% 2.56/1.01  fof(f31,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.56/1.01    inference(flattening,[],[f30])).
% 2.56/1.01  
% 2.56/1.01  fof(f67,plain,(
% 2.56/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.56/1.01    inference(cnf_transformation,[],[f31])).
% 2.56/1.01  
% 2.56/1.01  fof(f94,plain,(
% 2.56/1.01    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.56/1.01    inference(equality_resolution,[],[f67])).
% 2.56/1.01  
% 2.56/1.01  fof(f6,axiom,(
% 2.56/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.56/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.01  
% 2.56/1.01  fof(f21,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.56/1.01    inference(ennf_transformation,[],[f6])).
% 2.56/1.01  
% 2.56/1.01  fof(f22,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.56/1.01    inference(flattening,[],[f21])).
% 2.56/1.01  
% 2.56/1.01  fof(f61,plain,(
% 2.56/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.56/1.01    inference(cnf_transformation,[],[f22])).
% 2.56/1.01  
% 2.56/1.01  fof(f69,plain,(
% 2.56/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.56/1.01    inference(cnf_transformation,[],[f42])).
% 2.56/1.01  
% 2.56/1.01  fof(f95,plain,(
% 2.56/1.01    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.56/1.01    inference(equality_resolution,[],[f69])).
% 2.56/1.01  
% 2.56/1.01  fof(f9,axiom,(
% 2.56/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 2.56/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.01  
% 2.56/1.01  fof(f27,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.56/1.01    inference(ennf_transformation,[],[f9])).
% 2.56/1.01  
% 2.56/1.01  fof(f28,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.56/1.01    inference(flattening,[],[f27])).
% 2.56/1.01  
% 2.56/1.01  fof(f64,plain,(
% 2.56/1.01    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.56/1.01    inference(cnf_transformation,[],[f28])).
% 2.56/1.01  
% 2.56/1.01  fof(f2,axiom,(
% 2.56/1.01    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.56/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.01  
% 2.56/1.01  fof(f57,plain,(
% 2.56/1.01    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.56/1.01    inference(cnf_transformation,[],[f2])).
% 2.56/1.01  
% 2.56/1.01  fof(f3,axiom,(
% 2.56/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.56/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.01  
% 2.56/1.01  fof(f16,plain,(
% 2.56/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.56/1.01    inference(ennf_transformation,[],[f3])).
% 2.56/1.01  
% 2.56/1.01  fof(f17,plain,(
% 2.56/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.56/1.01    inference(flattening,[],[f16])).
% 2.56/1.01  
% 2.56/1.01  fof(f58,plain,(
% 2.56/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.56/1.01    inference(cnf_transformation,[],[f17])).
% 2.56/1.01  
% 2.56/1.01  fof(f1,axiom,(
% 2.56/1.01    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.56/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.01  
% 2.56/1.01  fof(f38,plain,(
% 2.56/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.56/1.01    inference(nnf_transformation,[],[f1])).
% 2.56/1.01  
% 2.56/1.01  fof(f39,plain,(
% 2.56/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.56/1.01    inference(rectify,[],[f38])).
% 2.56/1.01  
% 2.56/1.01  fof(f40,plain,(
% 2.56/1.01    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 2.56/1.01    introduced(choice_axiom,[])).
% 2.56/1.01  
% 2.56/1.01  fof(f41,plain,(
% 2.56/1.01    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.56/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 2.56/1.01  
% 2.56/1.01  fof(f53,plain,(
% 2.56/1.01    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.56/1.01    inference(cnf_transformation,[],[f41])).
% 2.56/1.01  
% 2.56/1.01  fof(f93,plain,(
% 2.56/1.01    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.56/1.01    inference(equality_resolution,[],[f53])).
% 2.56/1.01  
% 2.56/1.01  fof(f10,axiom,(
% 2.56/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.56/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.01  
% 2.56/1.01  fof(f29,plain,(
% 2.56/1.01    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.56/1.01    inference(ennf_transformation,[],[f10])).
% 2.56/1.01  
% 2.56/1.01  fof(f66,plain,(
% 2.56/1.01    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.56/1.01    inference(cnf_transformation,[],[f29])).
% 2.56/1.01  
% 2.56/1.01  fof(f88,plain,(
% 2.56/1.01    m1_subset_1(sK7,u1_struct_0(sK3))),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f84,plain,(
% 2.56/1.01    v1_tsep_1(sK3,sK2)),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f78,plain,(
% 2.56/1.01    m1_pre_topc(sK3,sK2)),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  fof(f77,plain,(
% 2.56/1.01    ~v2_struct_0(sK3)),
% 2.56/1.01    inference(cnf_transformation,[],[f52])).
% 2.56/1.01  
% 2.56/1.01  cnf(c_29,negated_conjecture,
% 2.56/1.01      ( m1_pre_topc(sK4,sK2) ),
% 2.56/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_1661,negated_conjecture,
% 2.56/1.01      ( m1_pre_topc(sK4,sK2) ),
% 2.56/1.01      inference(subtyping,[status(esa)],[c_29]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2396,plain,
% 2.56/1.01      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_1661]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_23,negated_conjecture,
% 2.56/1.01      ( m1_pre_topc(sK3,sK4) ),
% 2.56/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_1665,negated_conjecture,
% 2.56/1.01      ( m1_pre_topc(sK3,sK4) ),
% 2.56/1.01      inference(subtyping,[status(esa)],[c_23]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2392,plain,
% 2.56/1.01      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_1665]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_10,plain,
% 2.56/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.56/1.01      | ~ m1_pre_topc(X3,X4)
% 2.56/1.01      | ~ m1_pre_topc(X3,X1)
% 2.56/1.01      | ~ m1_pre_topc(X1,X4)
% 2.56/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.56/1.01      | ~ v1_funct_1(X0)
% 2.56/1.01      | v2_struct_0(X4)
% 2.56/1.01      | v2_struct_0(X2)
% 2.56/1.01      | ~ l1_pre_topc(X4)
% 2.56/1.01      | ~ l1_pre_topc(X2)
% 2.56/1.01      | ~ v2_pre_topc(X4)
% 2.56/1.01      | ~ v2_pre_topc(X2)
% 2.56/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.56/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_27,negated_conjecture,
% 2.56/1.01      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
% 2.56/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_758,plain,
% 2.56/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.56/1.01      | ~ m1_pre_topc(X0,X2)
% 2.56/1.01      | ~ m1_pre_topc(X1,X2)
% 2.56/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 2.56/1.01      | ~ v1_funct_1(X3)
% 2.56/1.01      | v2_struct_0(X4)
% 2.56/1.01      | v2_struct_0(X2)
% 2.56/1.01      | ~ l1_pre_topc(X4)
% 2.56/1.01      | ~ l1_pre_topc(X2)
% 2.56/1.01      | ~ v2_pre_topc(X4)
% 2.56/1.01      | ~ v2_pre_topc(X2)
% 2.56/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 2.56/1.01      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X4) != u1_struct_0(sK1)
% 2.56/1.01      | sK5 != X3 ),
% 2.56/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_759,plain,
% 2.56/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.56/1.01      | ~ m1_pre_topc(X0,X2)
% 2.56/1.01      | ~ m1_pre_topc(X1,X2)
% 2.56/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.56/1.01      | ~ v1_funct_1(sK5)
% 2.56/1.01      | v2_struct_0(X2)
% 2.56/1.01      | v2_struct_0(X3)
% 2.56/1.01      | ~ l1_pre_topc(X2)
% 2.56/1.01      | ~ l1_pre_topc(X3)
% 2.56/1.01      | ~ v2_pre_topc(X2)
% 2.56/1.01      | ~ v2_pre_topc(X3)
% 2.56/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 2.56/1.01      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 2.56/1.01      inference(unflattening,[status(thm)],[c_758]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_28,negated_conjecture,
% 2.56/1.01      ( v1_funct_1(sK5) ),
% 2.56/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_763,plain,
% 2.56/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.56/1.01      | ~ m1_pre_topc(X1,X2)
% 2.56/1.01      | ~ m1_pre_topc(X0,X2)
% 2.56/1.01      | ~ m1_pre_topc(X0,X1)
% 2.56/1.01      | v2_struct_0(X2)
% 2.56/1.01      | v2_struct_0(X3)
% 2.56/1.01      | ~ l1_pre_topc(X2)
% 2.56/1.01      | ~ l1_pre_topc(X3)
% 2.56/1.01      | ~ v2_pre_topc(X2)
% 2.56/1.01      | ~ v2_pre_topc(X3)
% 2.56/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 2.56/1.01      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 2.56/1.01      inference(global_propositional_subsumption,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_759,c_28]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_764,plain,
% 2.56/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.56/1.01      | ~ m1_pre_topc(X0,X2)
% 2.56/1.01      | ~ m1_pre_topc(X1,X2)
% 2.56/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.56/1.01      | v2_struct_0(X2)
% 2.56/1.01      | v2_struct_0(X3)
% 2.56/1.01      | ~ l1_pre_topc(X2)
% 2.56/1.01      | ~ l1_pre_topc(X3)
% 2.56/1.01      | ~ v2_pre_topc(X2)
% 2.56/1.01      | ~ v2_pre_topc(X3)
% 2.56/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 2.56/1.01      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 2.56/1.01      inference(renaming,[status(thm)],[c_763]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_17,plain,
% 2.56/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.56/1.01      | ~ m1_pre_topc(X2,X0)
% 2.56/1.01      | m1_pre_topc(X2,X1)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X1) ),
% 2.56/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_795,plain,
% 2.56/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.56/1.01      | ~ m1_pre_topc(X1,X2)
% 2.56/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.56/1.01      | v2_struct_0(X2)
% 2.56/1.01      | v2_struct_0(X3)
% 2.56/1.01      | ~ l1_pre_topc(X2)
% 2.56/1.01      | ~ l1_pre_topc(X3)
% 2.56/1.01      | ~ v2_pre_topc(X2)
% 2.56/1.01      | ~ v2_pre_topc(X3)
% 2.56/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 2.56/1.01      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 2.56/1.01      inference(forward_subsumption_resolution,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_764,c_17]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_1649,plain,
% 2.56/1.01      ( ~ m1_pre_topc(X0_54,X1_54)
% 2.56/1.01      | ~ m1_pre_topc(X1_54,X2_54)
% 2.56/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X3_54))))
% 2.56/1.01      | v2_struct_0(X2_54)
% 2.56/1.01      | v2_struct_0(X3_54)
% 2.56/1.01      | ~ l1_pre_topc(X2_54)
% 2.56/1.01      | ~ l1_pre_topc(X3_54)
% 2.56/1.01      | ~ v2_pre_topc(X2_54)
% 2.56/1.01      | ~ v2_pre_topc(X3_54)
% 2.56/1.01      | k2_partfun1(u1_struct_0(X1_54),u1_struct_0(X3_54),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X2_54,X3_54,X1_54,X0_54,sK5)
% 2.56/1.01      | u1_struct_0(X1_54) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X3_54) != u1_struct_0(sK1) ),
% 2.56/1.01      inference(subtyping,[status(esa)],[c_795]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2408,plain,
% 2.56/1.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK5,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,sK5)
% 2.56/1.01      | u1_struct_0(X0_54) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X1_54) != u1_struct_0(sK1)
% 2.56/1.01      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 2.56/1.01      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 2.56/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 2.56/1.01      | v2_struct_0(X3_54) = iProver_top
% 2.56/1.01      | v2_struct_0(X1_54) = iProver_top
% 2.56/1.01      | l1_pre_topc(X1_54) != iProver_top
% 2.56/1.01      | l1_pre_topc(X3_54) != iProver_top
% 2.56/1.01      | v2_pre_topc(X1_54) != iProver_top
% 2.56/1.01      | v2_pre_topc(X3_54) != iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_1649]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_4044,plain,
% 2.56/1.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK5,u1_struct_0(X1_54)) = k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK5)
% 2.56/1.01      | u1_struct_0(X0_54) != u1_struct_0(sK4)
% 2.56/1.01      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 2.56/1.01      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 2.56/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 2.56/1.01      | v2_struct_0(X2_54) = iProver_top
% 2.56/1.01      | v2_struct_0(sK1) = iProver_top
% 2.56/1.01      | l1_pre_topc(X2_54) != iProver_top
% 2.56/1.01      | l1_pre_topc(sK1) != iProver_top
% 2.56/1.01      | v2_pre_topc(X2_54) != iProver_top
% 2.56/1.01      | v2_pre_topc(sK1) != iProver_top ),
% 2.56/1.01      inference(equality_resolution,[status(thm)],[c_2408]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_38,negated_conjecture,
% 2.56/1.01      ( ~ v2_struct_0(sK1) ),
% 2.56/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_39,plain,
% 2.56/1.01      ( v2_struct_0(sK1) != iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_37,negated_conjecture,
% 2.56/1.01      ( v2_pre_topc(sK1) ),
% 2.56/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_40,plain,
% 2.56/1.01      ( v2_pre_topc(sK1) = iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_36,negated_conjecture,
% 2.56/1.01      ( l1_pre_topc(sK1) ),
% 2.56/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_41,plain,
% 2.56/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_4691,plain,
% 2.56/1.01      ( v2_pre_topc(X2_54) != iProver_top
% 2.56/1.01      | v2_struct_0(X2_54) = iProver_top
% 2.56/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 2.56/1.01      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 2.56/1.01      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 2.56/1.01      | u1_struct_0(X0_54) != u1_struct_0(sK4)
% 2.56/1.01      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK5,u1_struct_0(X1_54)) = k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK5)
% 2.56/1.01      | l1_pre_topc(X2_54) != iProver_top ),
% 2.56/1.01      inference(global_propositional_subsumption,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_4044,c_39,c_40,c_41]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_4692,plain,
% 2.56/1.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK5,u1_struct_0(X1_54)) = k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK5)
% 2.56/1.01      | u1_struct_0(X0_54) != u1_struct_0(sK4)
% 2.56/1.01      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 2.56/1.01      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 2.56/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 2.56/1.01      | v2_struct_0(X2_54) = iProver_top
% 2.56/1.01      | l1_pre_topc(X2_54) != iProver_top
% 2.56/1.01      | v2_pre_topc(X2_54) != iProver_top ),
% 2.56/1.01      inference(renaming,[status(thm)],[c_4691]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_4703,plain,
% 2.56/1.01      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK4,X0_54,sK5)
% 2.56/1.01      | m1_pre_topc(X0_54,sK4) != iProver_top
% 2.56/1.01      | m1_pre_topc(sK4,X1_54) != iProver_top
% 2.56/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 2.56/1.01      | v2_struct_0(X1_54) = iProver_top
% 2.56/1.01      | l1_pre_topc(X1_54) != iProver_top
% 2.56/1.01      | v2_pre_topc(X1_54) != iProver_top ),
% 2.56/1.01      inference(equality_resolution,[status(thm)],[c_4692]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_26,negated_conjecture,
% 2.56/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
% 2.56/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_51,plain,
% 2.56/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_4932,plain,
% 2.56/1.01      ( m1_pre_topc(sK4,X1_54) != iProver_top
% 2.56/1.01      | m1_pre_topc(X0_54,sK4) != iProver_top
% 2.56/1.01      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK4,X0_54,sK5)
% 2.56/1.01      | v2_struct_0(X1_54) = iProver_top
% 2.56/1.01      | l1_pre_topc(X1_54) != iProver_top
% 2.56/1.01      | v2_pre_topc(X1_54) != iProver_top ),
% 2.56/1.01      inference(global_propositional_subsumption,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_4703,c_51]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_4933,plain,
% 2.56/1.01      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK4,X0_54,sK5)
% 2.56/1.01      | m1_pre_topc(X0_54,sK4) != iProver_top
% 2.56/1.01      | m1_pre_topc(sK4,X1_54) != iProver_top
% 2.56/1.01      | v2_struct_0(X1_54) = iProver_top
% 2.56/1.01      | l1_pre_topc(X1_54) != iProver_top
% 2.56/1.01      | v2_pre_topc(X1_54) != iProver_top ),
% 2.56/1.01      inference(renaming,[status(thm)],[c_4932]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_4944,plain,
% 2.56/1.01      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(X0_54,sK1,sK4,sK3,sK5)
% 2.56/1.01      | m1_pre_topc(sK4,X0_54) != iProver_top
% 2.56/1.01      | v2_struct_0(X0_54) = iProver_top
% 2.56/1.01      | l1_pre_topc(X0_54) != iProver_top
% 2.56/1.01      | v2_pre_topc(X0_54) != iProver_top ),
% 2.56/1.01      inference(superposition,[status(thm)],[c_2392,c_4933]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_9,plain,
% 2.56/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.56/1.01      | ~ m1_pre_topc(X3,X1)
% 2.56/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.56/1.01      | ~ v1_funct_1(X0)
% 2.56/1.01      | v2_struct_0(X1)
% 2.56/1.01      | v2_struct_0(X2)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ l1_pre_topc(X2)
% 2.56/1.01      | ~ v2_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X2)
% 2.56/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.56/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_809,plain,
% 2.56/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.56/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.56/1.01      | ~ v1_funct_1(X2)
% 2.56/1.01      | v2_struct_0(X1)
% 2.56/1.01      | v2_struct_0(X3)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ l1_pre_topc(X3)
% 2.56/1.01      | ~ v2_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X3)
% 2.56/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 2.56/1.01      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X3) != u1_struct_0(sK1)
% 2.56/1.01      | sK5 != X2 ),
% 2.56/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_810,plain,
% 2.56/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.56/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.56/1.01      | ~ v1_funct_1(sK5)
% 2.56/1.01      | v2_struct_0(X1)
% 2.56/1.01      | v2_struct_0(X2)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ l1_pre_topc(X2)
% 2.56/1.01      | ~ v2_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X2)
% 2.56/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
% 2.56/1.01      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 2.56/1.01      inference(unflattening,[status(thm)],[c_809]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_814,plain,
% 2.56/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.56/1.01      | ~ m1_pre_topc(X0,X1)
% 2.56/1.01      | v2_struct_0(X1)
% 2.56/1.01      | v2_struct_0(X2)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ l1_pre_topc(X2)
% 2.56/1.01      | ~ v2_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X2)
% 2.56/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
% 2.56/1.01      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 2.56/1.01      inference(global_propositional_subsumption,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_810,c_28]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_815,plain,
% 2.56/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.56/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.56/1.01      | v2_struct_0(X1)
% 2.56/1.01      | v2_struct_0(X2)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ l1_pre_topc(X2)
% 2.56/1.01      | ~ v2_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X2)
% 2.56/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK5,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK5,X0)
% 2.56/1.01      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 2.56/1.01      inference(renaming,[status(thm)],[c_814]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_1648,plain,
% 2.56/1.01      ( ~ m1_pre_topc(X0_54,X1_54)
% 2.56/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X2_54))))
% 2.56/1.01      | v2_struct_0(X1_54)
% 2.56/1.01      | v2_struct_0(X2_54)
% 2.56/1.01      | ~ l1_pre_topc(X1_54)
% 2.56/1.01      | ~ l1_pre_topc(X2_54)
% 2.56/1.01      | ~ v2_pre_topc(X1_54)
% 2.56/1.01      | ~ v2_pre_topc(X2_54)
% 2.56/1.01      | k2_partfun1(u1_struct_0(X1_54),u1_struct_0(X2_54),sK5,u1_struct_0(X0_54)) = k2_tmap_1(X1_54,X2_54,sK5,X0_54)
% 2.56/1.01      | u1_struct_0(X1_54) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X2_54) != u1_struct_0(sK1) ),
% 2.56/1.01      inference(subtyping,[status(esa)],[c_815]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2409,plain,
% 2.56/1.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK5,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,sK5,X2_54)
% 2.56/1.01      | u1_struct_0(X0_54) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X1_54) != u1_struct_0(sK1)
% 2.56/1.01      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 2.56/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 2.56/1.01      | v2_struct_0(X0_54) = iProver_top
% 2.56/1.01      | v2_struct_0(X1_54) = iProver_top
% 2.56/1.01      | l1_pre_topc(X0_54) != iProver_top
% 2.56/1.01      | l1_pre_topc(X1_54) != iProver_top
% 2.56/1.01      | v2_pre_topc(X0_54) != iProver_top
% 2.56/1.01      | v2_pre_topc(X1_54) != iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_1648]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_3870,plain,
% 2.56/1.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK5,u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,sK5,X1_54)
% 2.56/1.01      | u1_struct_0(X0_54) != u1_struct_0(sK4)
% 2.56/1.01      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 2.56/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 2.56/1.01      | v2_struct_0(X0_54) = iProver_top
% 2.56/1.01      | v2_struct_0(sK1) = iProver_top
% 2.56/1.01      | l1_pre_topc(X0_54) != iProver_top
% 2.56/1.01      | l1_pre_topc(sK1) != iProver_top
% 2.56/1.01      | v2_pre_topc(X0_54) != iProver_top
% 2.56/1.01      | v2_pre_topc(sK1) != iProver_top ),
% 2.56/1.01      inference(equality_resolution,[status(thm)],[c_2409]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_3961,plain,
% 2.56/1.01      ( v2_pre_topc(X0_54) != iProver_top
% 2.56/1.01      | v2_struct_0(X0_54) = iProver_top
% 2.56/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 2.56/1.01      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 2.56/1.01      | u1_struct_0(X0_54) != u1_struct_0(sK4)
% 2.56/1.01      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK5,u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,sK5,X1_54)
% 2.56/1.01      | l1_pre_topc(X0_54) != iProver_top ),
% 2.56/1.01      inference(global_propositional_subsumption,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_3870,c_39,c_40,c_41]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_3962,plain,
% 2.56/1.01      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),sK5,u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,sK5,X1_54)
% 2.56/1.01      | u1_struct_0(X0_54) != u1_struct_0(sK4)
% 2.56/1.01      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 2.56/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 2.56/1.01      | v2_struct_0(X0_54) = iProver_top
% 2.56/1.01      | l1_pre_topc(X0_54) != iProver_top
% 2.56/1.01      | v2_pre_topc(X0_54) != iProver_top ),
% 2.56/1.01      inference(renaming,[status(thm)],[c_3961]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_3972,plain,
% 2.56/1.01      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK4,sK1,sK5,X0_54)
% 2.56/1.01      | m1_pre_topc(X0_54,sK4) != iProver_top
% 2.56/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 2.56/1.01      | v2_struct_0(sK4) = iProver_top
% 2.56/1.01      | l1_pre_topc(sK4) != iProver_top
% 2.56/1.01      | v2_pre_topc(sK4) != iProver_top ),
% 2.56/1.01      inference(equality_resolution,[status(thm)],[c_3962]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_34,negated_conjecture,
% 2.56/1.01      ( v2_pre_topc(sK2) ),
% 2.56/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_43,plain,
% 2.56/1.01      ( v2_pre_topc(sK2) = iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_33,negated_conjecture,
% 2.56/1.01      ( l1_pre_topc(sK2) ),
% 2.56/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_44,plain,
% 2.56/1.01      ( l1_pre_topc(sK2) = iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_30,negated_conjecture,
% 2.56/1.01      ( ~ v2_struct_0(sK4) ),
% 2.56/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_47,plain,
% 2.56/1.01      ( v2_struct_0(sK4) != iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_48,plain,
% 2.56/1.01      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_6,plain,
% 2.56/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X1)
% 2.56/1.01      | v2_pre_topc(X0) ),
% 2.56/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_1677,plain,
% 2.56/1.01      ( ~ m1_pre_topc(X0_54,X1_54)
% 2.56/1.01      | ~ l1_pre_topc(X1_54)
% 2.56/1.01      | ~ v2_pre_topc(X1_54)
% 2.56/1.01      | v2_pre_topc(X0_54) ),
% 2.56/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2381,plain,
% 2.56/1.01      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 2.56/1.01      | l1_pre_topc(X1_54) != iProver_top
% 2.56/1.01      | v2_pre_topc(X1_54) != iProver_top
% 2.56/1.01      | v2_pre_topc(X0_54) = iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_1677]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2898,plain,
% 2.56/1.01      ( l1_pre_topc(sK2) != iProver_top
% 2.56/1.01      | v2_pre_topc(sK4) = iProver_top
% 2.56/1.01      | v2_pre_topc(sK2) != iProver_top ),
% 2.56/1.01      inference(superposition,[status(thm)],[c_2396,c_2381]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_7,plain,
% 2.56/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.56/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_1676,plain,
% 2.56/1.01      ( ~ m1_pre_topc(X0_54,X1_54)
% 2.56/1.01      | ~ l1_pre_topc(X1_54)
% 2.56/1.01      | l1_pre_topc(X0_54) ),
% 2.56/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2937,plain,
% 2.56/1.01      ( ~ m1_pre_topc(sK4,X0_54)
% 2.56/1.01      | ~ l1_pre_topc(X0_54)
% 2.56/1.01      | l1_pre_topc(sK4) ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_1676]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_3036,plain,
% 2.56/1.01      ( ~ m1_pre_topc(sK4,sK2) | l1_pre_topc(sK4) | ~ l1_pre_topc(sK2) ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_2937]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_3037,plain,
% 2.56/1.01      ( m1_pre_topc(sK4,sK2) != iProver_top
% 2.56/1.01      | l1_pre_topc(sK4) = iProver_top
% 2.56/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_3036]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_4594,plain,
% 2.56/1.01      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK4,sK1,sK5,X0_54)
% 2.56/1.01      | m1_pre_topc(X0_54,sK4) != iProver_top ),
% 2.56/1.01      inference(global_propositional_subsumption,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_3972,c_43,c_44,c_47,c_48,c_51,c_2898,c_3037]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_4602,plain,
% 2.56/1.01      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
% 2.56/1.01      inference(superposition,[status(thm)],[c_2392,c_4594]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_4945,plain,
% 2.56/1.01      ( k3_tmap_1(X0_54,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
% 2.56/1.01      | m1_pre_topc(sK4,X0_54) != iProver_top
% 2.56/1.01      | v2_struct_0(X0_54) = iProver_top
% 2.56/1.01      | l1_pre_topc(X0_54) != iProver_top
% 2.56/1.01      | v2_pre_topc(X0_54) != iProver_top ),
% 2.56/1.01      inference(light_normalisation,[status(thm)],[c_4944,c_4602]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_4955,plain,
% 2.56/1.01      ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3)
% 2.56/1.01      | v2_struct_0(sK2) = iProver_top
% 2.56/1.01      | l1_pre_topc(sK2) != iProver_top
% 2.56/1.01      | v2_pre_topc(sK2) != iProver_top ),
% 2.56/1.01      inference(superposition,[status(thm)],[c_2396,c_4945]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_35,negated_conjecture,
% 2.56/1.01      ( ~ v2_struct_0(sK2) ),
% 2.56/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_42,plain,
% 2.56/1.01      ( v2_struct_0(sK2) != iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_5030,plain,
% 2.56/1.01      ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k2_tmap_1(sK4,sK1,sK5,sK3) ),
% 2.56/1.01      inference(global_propositional_subsumption,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_4955,c_42,c_43,c_44]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_18,negated_conjecture,
% 2.56/1.01      ( ~ r1_tmap_1(sK4,sK1,sK5,sK6)
% 2.56/1.01      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
% 2.56/1.01      inference(cnf_transformation,[],[f91]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_1670,negated_conjecture,
% 2.56/1.01      ( ~ r1_tmap_1(sK4,sK1,sK5,sK6)
% 2.56/1.01      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
% 2.56/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2388,plain,
% 2.56/1.01      ( r1_tmap_1(sK4,sK1,sK5,sK6) != iProver_top
% 2.56/1.01      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_1670]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_20,negated_conjecture,
% 2.56/1.01      ( sK6 = sK7 ),
% 2.56/1.01      inference(cnf_transformation,[],[f89]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_1668,negated_conjecture,
% 2.56/1.01      ( sK6 = sK7 ),
% 2.56/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2466,plain,
% 2.56/1.01      ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 2.56/1.01      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
% 2.56/1.01      inference(light_normalisation,[status(thm)],[c_2388,c_1668]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_5034,plain,
% 2.56/1.01      ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 2.56/1.01      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) != iProver_top ),
% 2.56/1.01      inference(demodulation,[status(thm)],[c_5030,c_2466]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_19,negated_conjecture,
% 2.56/1.01      ( r1_tmap_1(sK4,sK1,sK5,sK6)
% 2.56/1.01      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
% 2.56/1.01      inference(cnf_transformation,[],[f90]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_1669,negated_conjecture,
% 2.56/1.01      ( r1_tmap_1(sK4,sK1,sK5,sK6)
% 2.56/1.01      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
% 2.56/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2389,plain,
% 2.56/1.01      ( r1_tmap_1(sK4,sK1,sK5,sK6) = iProver_top
% 2.56/1.01      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
% 2.56/1.01      inference(predicate_to_equality,[status(thm)],[c_1669]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2455,plain,
% 2.56/1.01      ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 2.56/1.01      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
% 2.56/1.01      inference(light_normalisation,[status(thm)],[c_2389,c_1668]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_5033,plain,
% 2.56/1.01      ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 2.56/1.01      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) = iProver_top ),
% 2.56/1.01      inference(demodulation,[status(thm)],[c_5030,c_2455]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_16,plain,
% 2.56/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.56/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.56/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.56/1.01      | ~ v1_tsep_1(X4,X0)
% 2.56/1.01      | ~ m1_pre_topc(X4,X0)
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.56/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.56/1.01      | ~ v1_funct_1(X2)
% 2.56/1.01      | v2_struct_0(X1)
% 2.56/1.01      | v2_struct_0(X0)
% 2.56/1.01      | v2_struct_0(X4)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ l1_pre_topc(X0)
% 2.56/1.01      | ~ v2_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X0) ),
% 2.56/1.01      inference(cnf_transformation,[],[f96]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_14,plain,
% 2.56/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.56/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.56/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.56/1.01      | ~ m1_pre_topc(X4,X0)
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.56/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.56/1.01      | ~ v1_funct_1(X2)
% 2.56/1.01      | v2_struct_0(X1)
% 2.56/1.01      | v2_struct_0(X0)
% 2.56/1.01      | v2_struct_0(X4)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ l1_pre_topc(X0)
% 2.56/1.01      | ~ v2_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X0) ),
% 2.56/1.01      inference(cnf_transformation,[],[f94]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_199,plain,
% 2.56/1.01      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.56/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.56/1.01      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.56/1.01      | ~ m1_pre_topc(X4,X0)
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.56/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.56/1.01      | ~ v1_funct_1(X2)
% 2.56/1.01      | v2_struct_0(X1)
% 2.56/1.01      | v2_struct_0(X0)
% 2.56/1.01      | v2_struct_0(X4)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ l1_pre_topc(X0)
% 2.56/1.01      | ~ v2_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X0) ),
% 2.56/1.01      inference(global_propositional_subsumption,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_16,c_14]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_200,plain,
% 2.56/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.56/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.56/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.56/1.01      | ~ m1_pre_topc(X4,X0)
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.56/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.56/1.01      | ~ v1_funct_1(X2)
% 2.56/1.01      | v2_struct_0(X0)
% 2.56/1.01      | v2_struct_0(X1)
% 2.56/1.01      | v2_struct_0(X4)
% 2.56/1.01      | ~ l1_pre_topc(X0)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X0)
% 2.56/1.01      | ~ v2_pre_topc(X1) ),
% 2.56/1.01      inference(renaming,[status(thm)],[c_199]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_854,plain,
% 2.56/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.56/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.56/1.01      | ~ m1_pre_topc(X4,X0)
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.56/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.56/1.01      | ~ v1_funct_1(X2)
% 2.56/1.01      | v2_struct_0(X0)
% 2.56/1.01      | v2_struct_0(X1)
% 2.56/1.01      | v2_struct_0(X4)
% 2.56/1.01      | ~ l1_pre_topc(X0)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X0)
% 2.56/1.01      | ~ v2_pre_topc(X1)
% 2.56/1.01      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.56/1.01      | sK5 != X2 ),
% 2.56/1.01      inference(resolution_lifted,[status(thm)],[c_200,c_27]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_855,plain,
% 2.56/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.56/1.01      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.56/1.01      | ~ m1_pre_topc(X0,X2)
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.56/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.56/1.01      | ~ v1_funct_1(sK5)
% 2.56/1.01      | v2_struct_0(X2)
% 2.56/1.01      | v2_struct_0(X1)
% 2.56/1.01      | v2_struct_0(X0)
% 2.56/1.01      | ~ l1_pre_topc(X2)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X2)
% 2.56/1.01      | ~ v2_pre_topc(X1)
% 2.56/1.01      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.56/1.01      inference(unflattening,[status(thm)],[c_854]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_859,plain,
% 2.56/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.56/1.01      | ~ m1_pre_topc(X0,X2)
% 2.56/1.01      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.56/1.01      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.56/1.01      | v2_struct_0(X2)
% 2.56/1.01      | v2_struct_0(X1)
% 2.56/1.01      | v2_struct_0(X0)
% 2.56/1.01      | ~ l1_pre_topc(X2)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X2)
% 2.56/1.01      | ~ v2_pre_topc(X1)
% 2.56/1.01      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.56/1.01      inference(global_propositional_subsumption,
% 2.56/1.01                [status(thm)],
% 2.56/1.01                [c_855,c_28]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_860,plain,
% 2.56/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.56/1.01      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.56/1.01      | ~ m1_pre_topc(X0,X2)
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.56/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.56/1.01      | v2_struct_0(X0)
% 2.56/1.01      | v2_struct_0(X1)
% 2.56/1.01      | v2_struct_0(X2)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ l1_pre_topc(X2)
% 2.56/1.01      | ~ v2_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X2)
% 2.56/1.01      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.56/1.01      inference(renaming,[status(thm)],[c_859]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_8,plain,
% 2.56/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.56/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.56/1.01      | m1_subset_1(X2,u1_struct_0(X1))
% 2.56/1.01      | v2_struct_0(X1)
% 2.56/1.01      | v2_struct_0(X0)
% 2.56/1.01      | ~ l1_pre_topc(X1) ),
% 2.56/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_895,plain,
% 2.56/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.56/1.01      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 2.56/1.01      | ~ m1_pre_topc(X0,X2)
% 2.56/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.56/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.56/1.01      | v2_struct_0(X0)
% 2.56/1.01      | v2_struct_0(X1)
% 2.56/1.01      | v2_struct_0(X2)
% 2.56/1.01      | ~ l1_pre_topc(X1)
% 2.56/1.01      | ~ l1_pre_topc(X2)
% 2.56/1.01      | ~ v2_pre_topc(X1)
% 2.56/1.01      | ~ v2_pre_topc(X2)
% 2.56/1.01      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.56/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_860,c_8]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_1647,plain,
% 2.56/1.01      ( r1_tmap_1(X0_54,X1_54,k2_tmap_1(X2_54,X1_54,sK5,X0_54),X0_55)
% 2.56/1.01      | ~ r1_tmap_1(X2_54,X1_54,sK5,X0_55)
% 2.56/1.01      | ~ m1_pre_topc(X0_54,X2_54)
% 2.56/1.01      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 2.56/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 2.56/1.01      | v2_struct_0(X0_54)
% 2.56/1.01      | v2_struct_0(X1_54)
% 2.56/1.01      | v2_struct_0(X2_54)
% 2.56/1.01      | ~ l1_pre_topc(X1_54)
% 2.56/1.01      | ~ l1_pre_topc(X2_54)
% 2.56/1.01      | ~ v2_pre_topc(X1_54)
% 2.56/1.01      | ~ v2_pre_topc(X2_54)
% 2.56/1.01      | u1_struct_0(X2_54) != u1_struct_0(sK4)
% 2.56/1.01      | u1_struct_0(X1_54) != u1_struct_0(sK1) ),
% 2.56/1.01      inference(subtyping,[status(esa)],[c_895]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_2727,plain,
% 2.56/1.01      ( r1_tmap_1(X0_54,X1_54,k2_tmap_1(sK4,X1_54,sK5,X0_54),X0_55)
% 2.56/1.01      | ~ r1_tmap_1(sK4,X1_54,sK5,X0_55)
% 2.56/1.01      | ~ m1_pre_topc(X0_54,sK4)
% 2.56/1.01      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 2.56/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_54))))
% 2.56/1.01      | v2_struct_0(X0_54)
% 2.56/1.01      | v2_struct_0(X1_54)
% 2.56/1.01      | v2_struct_0(sK4)
% 2.56/1.01      | ~ l1_pre_topc(X1_54)
% 2.56/1.01      | ~ l1_pre_topc(sK4)
% 2.56/1.01      | ~ v2_pre_topc(X1_54)
% 2.56/1.01      | ~ v2_pre_topc(sK4)
% 2.56/1.01      | u1_struct_0(X1_54) != u1_struct_0(sK1)
% 2.56/1.01      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_1647]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_3450,plain,
% 2.56/1.01      ( ~ r1_tmap_1(sK4,X0_54,sK5,X0_55)
% 2.56/1.01      | r1_tmap_1(sK3,X0_54,k2_tmap_1(sK4,X0_54,sK5,sK3),X0_55)
% 2.56/1.01      | ~ m1_pre_topc(sK3,sK4)
% 2.56/1.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.56/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
% 2.56/1.01      | v2_struct_0(X0_54)
% 2.56/1.01      | v2_struct_0(sK4)
% 2.56/1.01      | v2_struct_0(sK3)
% 2.56/1.01      | ~ l1_pre_topc(X0_54)
% 2.56/1.01      | ~ l1_pre_topc(sK4)
% 2.56/1.01      | ~ v2_pre_topc(X0_54)
% 2.56/1.01      | ~ v2_pre_topc(sK4)
% 2.56/1.01      | u1_struct_0(X0_54) != u1_struct_0(sK1)
% 2.56/1.01      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.56/1.01      inference(instantiation,[status(thm)],[c_2727]) ).
% 2.56/1.01  
% 2.56/1.01  cnf(c_4444,plain,
% 2.56/1.01      ( ~ r1_tmap_1(sK4,X0_54,sK5,sK7)
% 2.56/1.01      | r1_tmap_1(sK3,X0_54,k2_tmap_1(sK4,X0_54,sK5,sK3),sK7)
% 2.56/1.01      | ~ m1_pre_topc(sK3,sK4)
% 2.56/1.01      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.56/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
% 2.56/1.01      | v2_struct_0(X0_54)
% 2.56/1.01      | v2_struct_0(sK4)
% 2.56/1.01      | v2_struct_0(sK3)
% 2.56/1.01      | ~ l1_pre_topc(X0_54)
% 2.56/1.01      | ~ l1_pre_topc(sK4)
% 2.56/1.01      | ~ v2_pre_topc(X0_54)
% 2.56/1.02      | ~ v2_pre_topc(sK4)
% 2.56/1.02      | u1_struct_0(X0_54) != u1_struct_0(sK1)
% 2.56/1.02      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_3450]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_4445,plain,
% 2.56/1.02      ( u1_struct_0(X0_54) != u1_struct_0(sK1)
% 2.56/1.02      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.56/1.02      | r1_tmap_1(sK4,X0_54,sK5,sK7) != iProver_top
% 2.56/1.02      | r1_tmap_1(sK3,X0_54,k2_tmap_1(sK4,X0_54,sK5,sK3),sK7) = iProver_top
% 2.56/1.02      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.56/1.02      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.56/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 2.56/1.02      | v2_struct_0(X0_54) = iProver_top
% 2.56/1.02      | v2_struct_0(sK4) = iProver_top
% 2.56/1.02      | v2_struct_0(sK3) = iProver_top
% 2.56/1.02      | l1_pre_topc(X0_54) != iProver_top
% 2.56/1.02      | l1_pre_topc(sK4) != iProver_top
% 2.56/1.02      | v2_pre_topc(X0_54) != iProver_top
% 2.56/1.02      | v2_pre_topc(sK4) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_4444]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_4447,plain,
% 2.56/1.02      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.56/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.56/1.02      | r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 2.56/1.02      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) = iProver_top
% 2.56/1.02      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.56/1.02      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.56/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 2.56/1.02      | v2_struct_0(sK4) = iProver_top
% 2.56/1.02      | v2_struct_0(sK1) = iProver_top
% 2.56/1.02      | v2_struct_0(sK3) = iProver_top
% 2.56/1.02      | l1_pre_topc(sK4) != iProver_top
% 2.56/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.56/1.02      | v2_pre_topc(sK4) != iProver_top
% 2.56/1.02      | v2_pre_topc(sK1) != iProver_top ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_4445]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1679,plain,( X0_55 = X0_55 ),theory(equality) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3705,plain,
% 2.56/1.02      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_1679]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_15,plain,
% 2.56/1.02      ( r1_tmap_1(X0,X1,X2,X3)
% 2.56/1.02      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.56/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.56/1.02      | ~ v1_tsep_1(X4,X0)
% 2.56/1.02      | ~ m1_pre_topc(X4,X0)
% 2.56/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.56/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.56/1.02      | ~ v1_funct_1(X2)
% 2.56/1.02      | v2_struct_0(X1)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | v2_struct_0(X4)
% 2.56/1.02      | ~ l1_pre_topc(X1)
% 2.56/1.02      | ~ l1_pre_topc(X0)
% 2.56/1.02      | ~ v2_pre_topc(X1)
% 2.56/1.02      | ~ v2_pre_topc(X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f95]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_911,plain,
% 2.56/1.02      ( r1_tmap_1(X0,X1,X2,X3)
% 2.56/1.02      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.56/1.02      | ~ v1_tsep_1(X4,X0)
% 2.56/1.02      | ~ m1_pre_topc(X4,X0)
% 2.56/1.02      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.56/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.56/1.02      | ~ v1_funct_1(X2)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | v2_struct_0(X1)
% 2.56/1.02      | v2_struct_0(X4)
% 2.56/1.02      | ~ l1_pre_topc(X0)
% 2.56/1.02      | ~ l1_pre_topc(X1)
% 2.56/1.02      | ~ v2_pre_topc(X0)
% 2.56/1.02      | ~ v2_pre_topc(X1)
% 2.56/1.02      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.56/1.02      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.56/1.02      | sK5 != X2 ),
% 2.56/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_912,plain,
% 2.56/1.02      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.56/1.02      | r1_tmap_1(X2,X1,sK5,X3)
% 2.56/1.02      | ~ v1_tsep_1(X0,X2)
% 2.56/1.02      | ~ m1_pre_topc(X0,X2)
% 2.56/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.56/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.56/1.02      | ~ v1_funct_1(sK5)
% 2.56/1.02      | v2_struct_0(X2)
% 2.56/1.02      | v2_struct_0(X1)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | ~ l1_pre_topc(X2)
% 2.56/1.02      | ~ l1_pre_topc(X1)
% 2.56/1.02      | ~ v2_pre_topc(X2)
% 2.56/1.02      | ~ v2_pre_topc(X1)
% 2.56/1.02      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.56/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.56/1.02      inference(unflattening,[status(thm)],[c_911]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_916,plain,
% 2.56/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.56/1.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.56/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_pre_topc(X0,X2)
% 2.56/1.02      | ~ v1_tsep_1(X0,X2)
% 2.56/1.02      | r1_tmap_1(X2,X1,sK5,X3)
% 2.56/1.02      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.56/1.02      | v2_struct_0(X2)
% 2.56/1.02      | v2_struct_0(X1)
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | ~ l1_pre_topc(X2)
% 2.56/1.02      | ~ l1_pre_topc(X1)
% 2.56/1.02      | ~ v2_pre_topc(X2)
% 2.56/1.02      | ~ v2_pre_topc(X1)
% 2.56/1.02      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.56/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_912,c_28]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_917,plain,
% 2.56/1.02      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.56/1.02      | r1_tmap_1(X2,X1,sK5,X3)
% 2.56/1.02      | ~ v1_tsep_1(X0,X2)
% 2.56/1.02      | ~ m1_pre_topc(X0,X2)
% 2.56/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.56/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | v2_struct_0(X1)
% 2.56/1.02      | v2_struct_0(X2)
% 2.56/1.02      | ~ l1_pre_topc(X1)
% 2.56/1.02      | ~ l1_pre_topc(X2)
% 2.56/1.02      | ~ v2_pre_topc(X1)
% 2.56/1.02      | ~ v2_pre_topc(X2)
% 2.56/1.02      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.56/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.56/1.02      inference(renaming,[status(thm)],[c_916]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_954,plain,
% 2.56/1.02      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 2.56/1.02      | r1_tmap_1(X2,X1,sK5,X3)
% 2.56/1.02      | ~ v1_tsep_1(X0,X2)
% 2.56/1.02      | ~ m1_pre_topc(X0,X2)
% 2.56/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.56/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.56/1.02      | v2_struct_0(X0)
% 2.56/1.02      | v2_struct_0(X1)
% 2.56/1.02      | v2_struct_0(X2)
% 2.56/1.02      | ~ l1_pre_topc(X1)
% 2.56/1.02      | ~ l1_pre_topc(X2)
% 2.56/1.02      | ~ v2_pre_topc(X1)
% 2.56/1.02      | ~ v2_pre_topc(X2)
% 2.56/1.02      | u1_struct_0(X2) != u1_struct_0(sK4)
% 2.56/1.02      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.56/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_917,c_8]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1646,plain,
% 2.56/1.02      ( ~ r1_tmap_1(X0_54,X1_54,k2_tmap_1(X2_54,X1_54,sK5,X0_54),X0_55)
% 2.56/1.02      | r1_tmap_1(X2_54,X1_54,sK5,X0_55)
% 2.56/1.02      | ~ v1_tsep_1(X0_54,X2_54)
% 2.56/1.02      | ~ m1_pre_topc(X0_54,X2_54)
% 2.56/1.02      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 2.56/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 2.56/1.02      | v2_struct_0(X0_54)
% 2.56/1.02      | v2_struct_0(X1_54)
% 2.56/1.02      | v2_struct_0(X2_54)
% 2.56/1.02      | ~ l1_pre_topc(X1_54)
% 2.56/1.02      | ~ l1_pre_topc(X2_54)
% 2.56/1.02      | ~ v2_pre_topc(X1_54)
% 2.56/1.02      | ~ v2_pre_topc(X2_54)
% 2.56/1.02      | u1_struct_0(X2_54) != u1_struct_0(sK4)
% 2.56/1.02      | u1_struct_0(X1_54) != u1_struct_0(sK1) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_954]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2726,plain,
% 2.56/1.02      ( ~ r1_tmap_1(X0_54,X1_54,k2_tmap_1(sK4,X1_54,sK5,X0_54),X0_55)
% 2.56/1.02      | r1_tmap_1(sK4,X1_54,sK5,X0_55)
% 2.56/1.02      | ~ v1_tsep_1(X0_54,sK4)
% 2.56/1.02      | ~ m1_pre_topc(X0_54,sK4)
% 2.56/1.02      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 2.56/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_54))))
% 2.56/1.02      | v2_struct_0(X0_54)
% 2.56/1.02      | v2_struct_0(X1_54)
% 2.56/1.02      | v2_struct_0(sK4)
% 2.56/1.02      | ~ l1_pre_topc(X1_54)
% 2.56/1.02      | ~ l1_pre_topc(sK4)
% 2.56/1.02      | ~ v2_pre_topc(X1_54)
% 2.56/1.02      | ~ v2_pre_topc(sK4)
% 2.56/1.02      | u1_struct_0(X1_54) != u1_struct_0(sK1)
% 2.56/1.02      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_1646]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3455,plain,
% 2.56/1.02      ( r1_tmap_1(sK4,X0_54,sK5,X0_55)
% 2.56/1.02      | ~ r1_tmap_1(sK3,X0_54,k2_tmap_1(sK4,X0_54,sK5,sK3),X0_55)
% 2.56/1.02      | ~ v1_tsep_1(sK3,sK4)
% 2.56/1.02      | ~ m1_pre_topc(sK3,sK4)
% 2.56/1.02      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 2.56/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
% 2.56/1.02      | v2_struct_0(X0_54)
% 2.56/1.02      | v2_struct_0(sK4)
% 2.56/1.02      | v2_struct_0(sK3)
% 2.56/1.02      | ~ l1_pre_topc(X0_54)
% 2.56/1.02      | ~ l1_pre_topc(sK4)
% 2.56/1.02      | ~ v2_pre_topc(X0_54)
% 2.56/1.02      | ~ v2_pre_topc(sK4)
% 2.56/1.02      | u1_struct_0(X0_54) != u1_struct_0(sK1)
% 2.56/1.02      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_2726]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3624,plain,
% 2.56/1.02      ( r1_tmap_1(sK4,X0_54,sK5,sK7)
% 2.56/1.02      | ~ r1_tmap_1(sK3,X0_54,k2_tmap_1(sK4,X0_54,sK5,sK3),sK7)
% 2.56/1.02      | ~ v1_tsep_1(sK3,sK4)
% 2.56/1.02      | ~ m1_pre_topc(sK3,sK4)
% 2.56/1.02      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 2.56/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54))))
% 2.56/1.02      | v2_struct_0(X0_54)
% 2.56/1.02      | v2_struct_0(sK4)
% 2.56/1.02      | v2_struct_0(sK3)
% 2.56/1.02      | ~ l1_pre_topc(X0_54)
% 2.56/1.02      | ~ l1_pre_topc(sK4)
% 2.56/1.02      | ~ v2_pre_topc(X0_54)
% 2.56/1.02      | ~ v2_pre_topc(sK4)
% 2.56/1.02      | u1_struct_0(X0_54) != u1_struct_0(sK1)
% 2.56/1.02      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_3455]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3625,plain,
% 2.56/1.02      ( u1_struct_0(X0_54) != u1_struct_0(sK1)
% 2.56/1.02      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.56/1.02      | r1_tmap_1(sK4,X0_54,sK5,sK7) = iProver_top
% 2.56/1.02      | r1_tmap_1(sK3,X0_54,k2_tmap_1(sK4,X0_54,sK5,sK3),sK7) != iProver_top
% 2.56/1.02      | v1_tsep_1(sK3,sK4) != iProver_top
% 2.56/1.02      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.56/1.02      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.56/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_54)))) != iProver_top
% 2.56/1.02      | v2_struct_0(X0_54) = iProver_top
% 2.56/1.02      | v2_struct_0(sK4) = iProver_top
% 2.56/1.02      | v2_struct_0(sK3) = iProver_top
% 2.56/1.02      | l1_pre_topc(X0_54) != iProver_top
% 2.56/1.02      | l1_pre_topc(sK4) != iProver_top
% 2.56/1.02      | v2_pre_topc(X0_54) != iProver_top
% 2.56/1.02      | v2_pre_topc(sK4) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_3624]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3627,plain,
% 2.56/1.02      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.56/1.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.56/1.02      | r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 2.56/1.02      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK4,sK1,sK5,sK3),sK7) != iProver_top
% 2.56/1.02      | v1_tsep_1(sK3,sK4) != iProver_top
% 2.56/1.02      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.56/1.02      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.56/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 2.56/1.02      | v2_struct_0(sK4) = iProver_top
% 2.56/1.02      | v2_struct_0(sK1) = iProver_top
% 2.56/1.02      | v2_struct_0(sK3) = iProver_top
% 2.56/1.02      | l1_pre_topc(sK4) != iProver_top
% 2.56/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.56/1.02      | v2_pre_topc(sK4) != iProver_top
% 2.56/1.02      | v2_pre_topc(sK1) != iProver_top ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_3625]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_12,plain,
% 2.56/1.02      ( ~ v1_tsep_1(X0,X1)
% 2.56/1.02      | v1_tsep_1(X0,X2)
% 2.56/1.02      | ~ m1_pre_topc(X0,X1)
% 2.56/1.02      | ~ m1_pre_topc(X2,X1)
% 2.56/1.02      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 2.56/1.02      | v2_struct_0(X1)
% 2.56/1.02      | v2_struct_0(X2)
% 2.56/1.02      | ~ l1_pre_topc(X1)
% 2.56/1.02      | ~ v2_pre_topc(X1) ),
% 2.56/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1673,plain,
% 2.56/1.02      ( ~ v1_tsep_1(X0_54,X1_54)
% 2.56/1.02      | v1_tsep_1(X0_54,X2_54)
% 2.56/1.02      | ~ m1_pre_topc(X0_54,X1_54)
% 2.56/1.02      | ~ m1_pre_topc(X2_54,X1_54)
% 2.56/1.02      | ~ r1_tarski(u1_struct_0(X0_54),u1_struct_0(X2_54))
% 2.56/1.02      | v2_struct_0(X1_54)
% 2.56/1.02      | v2_struct_0(X2_54)
% 2.56/1.02      | ~ l1_pre_topc(X1_54)
% 2.56/1.02      | ~ v2_pre_topc(X1_54) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_12]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2810,plain,
% 2.56/1.02      ( v1_tsep_1(sK3,X0_54)
% 2.56/1.02      | ~ v1_tsep_1(sK3,sK2)
% 2.56/1.02      | ~ m1_pre_topc(X0_54,sK2)
% 2.56/1.02      | ~ m1_pre_topc(sK3,sK2)
% 2.56/1.02      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_54))
% 2.56/1.02      | v2_struct_0(X0_54)
% 2.56/1.02      | v2_struct_0(sK2)
% 2.56/1.02      | ~ l1_pre_topc(sK2)
% 2.56/1.02      | ~ v2_pre_topc(sK2) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_1673]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3007,plain,
% 2.56/1.02      ( v1_tsep_1(sK3,sK4)
% 2.56/1.02      | ~ v1_tsep_1(sK3,sK2)
% 2.56/1.02      | ~ m1_pre_topc(sK4,sK2)
% 2.56/1.02      | ~ m1_pre_topc(sK3,sK2)
% 2.56/1.02      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
% 2.56/1.02      | v2_struct_0(sK4)
% 2.56/1.02      | v2_struct_0(sK2)
% 2.56/1.02      | ~ l1_pre_topc(sK2)
% 2.56/1.02      | ~ v2_pre_topc(sK2) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_2810]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3008,plain,
% 2.56/1.02      ( v1_tsep_1(sK3,sK4) = iProver_top
% 2.56/1.02      | v1_tsep_1(sK3,sK2) != iProver_top
% 2.56/1.02      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.56/1.02      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.56/1.02      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 2.56/1.02      | v2_struct_0(sK4) = iProver_top
% 2.56/1.02      | v2_struct_0(sK2) = iProver_top
% 2.56/1.02      | l1_pre_topc(sK2) != iProver_top
% 2.56/1.02      | v2_pre_topc(sK2) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_3007]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_4,plain,
% 2.56/1.02      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.56/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_5,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.56/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_482,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 2.56/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_5]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_483,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.56/1.02      | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.56/1.02      inference(unflattening,[status(thm)],[c_482]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3,plain,
% 2.56/1.02      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.56/1.02      inference(cnf_transformation,[],[f93]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1128,plain,
% 2.56/1.02      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.56/1.02      inference(prop_impl,[status(thm)],[c_3]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1129,plain,
% 2.56/1.02      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.56/1.02      inference(renaming,[status(thm)],[c_1128]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1211,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.56/1.02      inference(bin_hyper_res,[status(thm)],[c_483,c_1129]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1652,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 2.56/1.02      | r1_tarski(X0_55,X1_55) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_1211]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2825,plain,
% 2.56/1.02      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.56/1.02      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_1652]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2826,plain,
% 2.56/1.02      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.56/1.02      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_2825]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_13,plain,
% 2.56/1.02      ( ~ m1_pre_topc(X0,X1)
% 2.56/1.02      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.56/1.02      | ~ l1_pre_topc(X1) ),
% 2.56/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1672,plain,
% 2.56/1.02      ( ~ m1_pre_topc(X0_54,X1_54)
% 2.56/1.02      | m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54)))
% 2.56/1.02      | ~ l1_pre_topc(X1_54) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2740,plain,
% 2.56/1.02      ( ~ m1_pre_topc(sK3,sK4)
% 2.56/1.02      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.56/1.02      | ~ l1_pre_topc(sK4) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_1672]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2741,plain,
% 2.56/1.02      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.56/1.02      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.56/1.02      | l1_pre_topc(sK4) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_2740]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2725,plain,
% 2.56/1.02      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_1679]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_21,negated_conjecture,
% 2.56/1.02      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.56/1.02      inference(cnf_transformation,[],[f88]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_56,plain,
% 2.56/1.02      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_54,plain,
% 2.56/1.02      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_25,negated_conjecture,
% 2.56/1.02      ( v1_tsep_1(sK3,sK2) ),
% 2.56/1.02      inference(cnf_transformation,[],[f84]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_52,plain,
% 2.56/1.02      ( v1_tsep_1(sK3,sK2) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_31,negated_conjecture,
% 2.56/1.02      ( m1_pre_topc(sK3,sK2) ),
% 2.56/1.02      inference(cnf_transformation,[],[f78]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_46,plain,
% 2.56/1.02      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_32,negated_conjecture,
% 2.56/1.02      ( ~ v2_struct_0(sK3) ),
% 2.56/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_45,plain,
% 2.56/1.02      ( v2_struct_0(sK3) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(contradiction,plain,
% 2.56/1.02      ( $false ),
% 2.56/1.02      inference(minisat,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_5034,c_5033,c_4447,c_3705,c_3627,c_3037,c_3008,c_2898,
% 2.56/1.02                 c_2826,c_2741,c_2725,c_56,c_54,c_52,c_51,c_48,c_47,c_46,
% 2.56/1.02                 c_45,c_44,c_43,c_42,c_41,c_40,c_39]) ).
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.56/1.02  
% 2.56/1.02  ------                               Statistics
% 2.56/1.02  
% 2.56/1.02  ------ General
% 2.56/1.02  
% 2.56/1.02  abstr_ref_over_cycles:                  0
% 2.56/1.02  abstr_ref_under_cycles:                 0
% 2.56/1.02  gc_basic_clause_elim:                   0
% 2.56/1.02  forced_gc_time:                         0
% 2.56/1.02  parsing_time:                           0.012
% 2.56/1.02  unif_index_cands_time:                  0.
% 2.56/1.02  unif_index_add_time:                    0.
% 2.56/1.02  orderings_time:                         0.
% 2.56/1.02  out_proof_time:                         0.016
% 2.56/1.02  total_time:                             0.195
% 2.56/1.02  num_of_symbols:                         59
% 2.56/1.02  num_of_terms:                           2732
% 2.56/1.02  
% 2.56/1.02  ------ Preprocessing
% 2.56/1.02  
% 2.56/1.02  num_of_splits:                          0
% 2.56/1.02  num_of_split_atoms:                     0
% 2.56/1.02  num_of_reused_defs:                     0
% 2.56/1.02  num_eq_ax_congr_red:                    34
% 2.56/1.02  num_of_sem_filtered_clauses:            1
% 2.56/1.02  num_of_subtypes:                        2
% 2.56/1.02  monotx_restored_types:                  0
% 2.56/1.02  sat_num_of_epr_types:                   0
% 2.56/1.02  sat_num_of_non_cyclic_types:            0
% 2.56/1.02  sat_guarded_non_collapsed_types:        0
% 2.56/1.02  num_pure_diseq_elim:                    0
% 2.56/1.02  simp_replaced_by:                       0
% 2.56/1.02  res_preprocessed:                       191
% 2.56/1.02  prep_upred:                             0
% 2.56/1.02  prep_unflattend:                        26
% 2.56/1.02  smt_new_axioms:                         0
% 2.56/1.02  pred_elim_cands:                        8
% 2.56/1.02  pred_elim:                              4
% 2.56/1.02  pred_elim_cl:                           6
% 2.56/1.02  pred_elim_cycles:                       9
% 2.56/1.02  merged_defs:                            14
% 2.56/1.02  merged_defs_ncl:                        0
% 2.56/1.02  bin_hyper_res:                          15
% 2.56/1.02  prep_cycles:                            5
% 2.56/1.02  pred_elim_time:                         0.017
% 2.56/1.02  splitting_time:                         0.
% 2.56/1.02  sem_filter_time:                        0.
% 2.56/1.02  monotx_time:                            0.
% 2.56/1.02  subtype_inf_time:                       0.
% 2.56/1.02  
% 2.56/1.02  ------ Problem properties
% 2.56/1.02  
% 2.56/1.02  clauses:                                32
% 2.56/1.02  conjectures:                            18
% 2.56/1.02  epr:                                    16
% 2.56/1.02  horn:                                   23
% 2.56/1.02  ground:                                 18
% 2.56/1.02  unary:                                  16
% 2.56/1.02  binary:                                 3
% 2.56/1.02  lits:                                   119
% 2.56/1.02  lits_eq:                                13
% 2.56/1.02  fd_pure:                                0
% 2.56/1.02  fd_pseudo:                              0
% 2.56/1.02  fd_cond:                                0
% 2.56/1.02  fd_pseudo_cond:                         0
% 2.56/1.02  ac_symbols:                             0
% 2.56/1.02  
% 2.56/1.02  ------ Propositional Solver
% 2.56/1.02  
% 2.56/1.02  prop_solver_calls:                      33
% 2.56/1.02  prop_fast_solver_calls:                 2017
% 2.56/1.02  smt_solver_calls:                       0
% 2.56/1.02  smt_fast_solver_calls:                  0
% 2.56/1.02  prop_num_of_clauses:                    1132
% 2.56/1.02  prop_preprocess_simplified:             5354
% 2.56/1.02  prop_fo_subsumed:                       70
% 2.56/1.02  prop_solver_time:                       0.
% 2.56/1.02  smt_solver_time:                        0.
% 2.56/1.02  smt_fast_solver_time:                   0.
% 2.56/1.02  prop_fast_solver_time:                  0.
% 2.56/1.02  prop_unsat_core_time:                   0.
% 2.56/1.02  
% 2.56/1.02  ------ QBF
% 2.56/1.02  
% 2.56/1.02  qbf_q_res:                              0
% 2.56/1.02  qbf_num_tautologies:                    0
% 2.56/1.02  qbf_prep_cycles:                        0
% 2.56/1.02  
% 2.56/1.02  ------ BMC1
% 2.56/1.02  
% 2.56/1.02  bmc1_current_bound:                     -1
% 2.56/1.02  bmc1_last_solved_bound:                 -1
% 2.56/1.02  bmc1_unsat_core_size:                   -1
% 2.56/1.02  bmc1_unsat_core_parents_size:           -1
% 2.56/1.02  bmc1_merge_next_fun:                    0
% 2.56/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.56/1.02  
% 2.56/1.02  ------ Instantiation
% 2.56/1.02  
% 2.56/1.02  inst_num_of_clauses:                    327
% 2.56/1.02  inst_num_in_passive:                    13
% 2.56/1.02  inst_num_in_active:                     268
% 2.56/1.02  inst_num_in_unprocessed:                46
% 2.56/1.02  inst_num_of_loops:                      320
% 2.56/1.02  inst_num_of_learning_restarts:          0
% 2.56/1.02  inst_num_moves_active_passive:          47
% 2.56/1.02  inst_lit_activity:                      0
% 2.56/1.02  inst_lit_activity_moves:                0
% 2.56/1.02  inst_num_tautologies:                   0
% 2.56/1.02  inst_num_prop_implied:                  0
% 2.56/1.02  inst_num_existing_simplified:           0
% 2.56/1.02  inst_num_eq_res_simplified:             0
% 2.56/1.02  inst_num_child_elim:                    0
% 2.56/1.02  inst_num_of_dismatching_blockings:      156
% 2.56/1.02  inst_num_of_non_proper_insts:           413
% 2.56/1.02  inst_num_of_duplicates:                 0
% 2.56/1.02  inst_inst_num_from_inst_to_res:         0
% 2.56/1.02  inst_dismatching_checking_time:         0.
% 2.56/1.02  
% 2.56/1.02  ------ Resolution
% 2.56/1.02  
% 2.56/1.02  res_num_of_clauses:                     0
% 2.56/1.02  res_num_in_passive:                     0
% 2.56/1.02  res_num_in_active:                      0
% 2.56/1.02  res_num_of_loops:                       196
% 2.56/1.02  res_forward_subset_subsumed:            71
% 2.56/1.02  res_backward_subset_subsumed:           0
% 2.56/1.02  res_forward_subsumed:                   0
% 2.56/1.02  res_backward_subsumed:                  0
% 2.56/1.02  res_forward_subsumption_resolution:     3
% 2.56/1.02  res_backward_subsumption_resolution:    0
% 2.56/1.02  res_clause_to_clause_subsumption:       240
% 2.56/1.02  res_orphan_elimination:                 0
% 2.56/1.02  res_tautology_del:                      115
% 2.56/1.02  res_num_eq_res_simplified:              0
% 2.56/1.02  res_num_sel_changes:                    0
% 2.56/1.02  res_moves_from_active_to_pass:          0
% 2.56/1.02  
% 2.56/1.02  ------ Superposition
% 2.56/1.02  
% 2.56/1.02  sup_time_total:                         0.
% 2.56/1.02  sup_time_generating:                    0.
% 2.56/1.02  sup_time_sim_full:                      0.
% 2.56/1.02  sup_time_sim_immed:                     0.
% 2.56/1.02  
% 2.56/1.02  sup_num_of_clauses:                     67
% 2.56/1.02  sup_num_in_active:                      61
% 2.56/1.02  sup_num_in_passive:                     6
% 2.56/1.02  sup_num_of_loops:                       63
% 2.56/1.02  sup_fw_superposition:                   31
% 2.56/1.02  sup_bw_superposition:                   9
% 2.56/1.02  sup_immediate_simplified:               8
% 2.56/1.02  sup_given_eliminated:                   0
% 2.56/1.02  comparisons_done:                       0
% 2.56/1.02  comparisons_avoided:                    0
% 2.56/1.02  
% 2.56/1.02  ------ Simplifications
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  sim_fw_subset_subsumed:                 7
% 2.56/1.02  sim_bw_subset_subsumed:                 0
% 2.56/1.02  sim_fw_subsumed:                        0
% 2.56/1.02  sim_bw_subsumed:                        0
% 2.56/1.02  sim_fw_subsumption_res:                 2
% 2.56/1.02  sim_bw_subsumption_res:                 0
% 2.56/1.02  sim_tautology_del:                      4
% 2.56/1.02  sim_eq_tautology_del:                   1
% 2.56/1.02  sim_eq_res_simp:                        0
% 2.56/1.02  sim_fw_demodulated:                     0
% 2.56/1.02  sim_bw_demodulated:                     2
% 2.56/1.02  sim_light_normalised:                   4
% 2.56/1.02  sim_joinable_taut:                      0
% 2.56/1.02  sim_joinable_simp:                      0
% 2.56/1.02  sim_ac_normalised:                      0
% 2.56/1.02  sim_smt_subsumption:                    0
% 2.56/1.02  
%------------------------------------------------------------------------------
