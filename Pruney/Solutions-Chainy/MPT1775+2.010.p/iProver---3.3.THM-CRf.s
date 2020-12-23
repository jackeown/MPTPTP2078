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
% DateTime   : Thu Dec  3 12:23:18 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  207 (1820 expanded)
%              Number of clauses        :  123 ( 383 expanded)
%              Number of leaves         :   21 ( 711 expanded)
%              Depth                    :   35
%              Number of atoms          : 1636 (32005 expanded)
%              Number of equality atoms :  235 (2243 expanded)
%              Maximal formula depth    :   32 (   8 average)
%              Maximal clause size      :   44 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & v1_tsep_1(X2,X3) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X1,X4,X5)
                                    <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            | ~ r1_tmap_1(X3,X1,X4,X5) )
          & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            | r1_tmap_1(X3,X1,X4,X5) )
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6)
          | ~ r1_tmap_1(X3,X1,X4,X5) )
        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6)
          | r1_tmap_1(X3,X1,X4,X5) )
        & sK6 = X5
        & m1_subset_1(sK6,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                | ~ r1_tmap_1(X3,X1,X4,X5) )
              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                | r1_tmap_1(X3,X1,X4,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              | ~ r1_tmap_1(X3,X1,X4,sK5) )
            & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              | r1_tmap_1(X3,X1,X4,sK5) )
            & sK5 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                    | ~ r1_tmap_1(X3,X1,X4,X5) )
                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                    | r1_tmap_1(X3,X1,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_pre_topc(X2,X3)
          & v1_tsep_1(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6)
                  | ~ r1_tmap_1(X3,X1,sK4,X5) )
                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6)
                  | r1_tmap_1(X3,X1,sK4,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & v1_tsep_1(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                        | ~ r1_tmap_1(X3,X1,X4,X5) )
                      & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                        | r1_tmap_1(X3,X1,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(X2,X3)
              & v1_tsep_1(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6)
                      | ~ r1_tmap_1(sK3,X1,X4,X5) )
                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6)
                      | r1_tmap_1(sK3,X1,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & m1_pre_topc(X2,sK3)
            & v1_tsep_1(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,X1,X4,X5) )
                          & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                            | r1_tmap_1(X3,X1,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & v1_tsep_1(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6)
                          | ~ r1_tmap_1(X3,X1,X4,X5) )
                        & ( r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6)
                          | r1_tmap_1(X3,X1,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK2,X3)
                & v1_tsep_1(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,sK1,X4,X5) )
                            & ( r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6)
                              | r1_tmap_1(X3,sK1,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & v1_tsep_1(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X1,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & v1_tsep_1(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
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
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
      | ~ r1_tmap_1(sK3,sK1,sK4,sK5) )
    & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
      | r1_tmap_1(sK3,sK1,sK4,sK5) )
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_pre_topc(sK2,sK3)
    & v1_tsep_1(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f40,f47,f46,f45,f44,f43,f42,f41])).

fof(f85,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(flattening,[],[f31])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(nnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f66])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f86,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X6)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f65])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
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
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
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
    inference(equality_resolution,[],[f64])).

cnf(c_12,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1318,plain,
    ( m1_pre_topc(X0_53,X0_53)
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1979,plain,
    ( m1_pre_topc(X0_53,X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1318])).

cnf(c_13,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1317,plain,
    ( r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1980,plain,
    ( r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53)) = iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1317])).

cnf(c_19,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1314,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1983,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1314])).

cnf(c_20,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1313,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2073,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1983,c_1313])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r2_hidden(X3,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_10,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_206,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_11])).

cnf(c_207,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_206])).

cnf(c_24,negated_conjecture,
    ( v1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_489,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_207,c_24])).

cnf(c_490,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_492,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_23])).

cnf(c_510,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ r2_hidden(X3,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(sK2) != X6
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_492])).

cnf(c_511,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,X3),X4)
    | r1_tmap_1(sK3,X1,X3,X4)
    | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X2)
    | ~ r2_hidden(X4,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_515,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK3,X2)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
    | r1_tmap_1(sK3,X1,X3,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,X3),X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_29])).

cnf(c_516,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,X3),X4)
    | r1_tmap_1(sK3,X1,X3,X4)
    | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X2)
    | ~ r2_hidden(X4,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(sK3) ),
    inference(renaming,[status(thm)],[c_515])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_565,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,X3),X4)
    | r1_tmap_1(sK3,X1,X3,X4)
    | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X2)
    | ~ r2_hidden(X4,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_516,c_4,c_6,c_14])).

cnf(c_639,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,X3),X4)
    | r1_tmap_1(sK3,X1,X3,X4)
    | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X2)
    | ~ m1_subset_1(X5,X6)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X6)
    | X4 != X5
    | u1_struct_0(sK2) != X6 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_565])).

cnf(c_640,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,X3),X4)
    | r1_tmap_1(sK3,X1,X3,X4)
    | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(X4,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_881,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,X3),X4)
    | r1_tmap_1(sK3,X1,X3,X4)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(X4,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v1_xboole_0(u1_struct_0(sK2))
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_640])).

cnf(c_882,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),X3)
    | r1_tmap_1(sK3,X1,sK4,X3)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v1_xboole_0(u1_struct_0(sK2))
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_881])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_886,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(sK3,X2)
    | ~ m1_pre_topc(X0,sK3)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | r1_tmap_1(sK3,X1,sK4,X3)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v1_xboole_0(u1_struct_0(sK2))
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_882,c_27])).

cnf(c_887,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),X3)
    | r1_tmap_1(sK3,X1,sK4,X3)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v1_xboole_0(u1_struct_0(sK2))
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_886])).

cnf(c_1296,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,sK3,X0_53,sK4),X0_54)
    | r1_tmap_1(sK3,X1_53,sK4,X0_54)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_53))
    | ~ m1_pre_topc(X0_53,sK3)
    | ~ m1_pre_topc(sK3,X2_53)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | v1_xboole_0(u1_struct_0(sK2))
    | u1_struct_0(X1_53) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_887])).

cnf(c_1324,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,sK3,X0_53,sK4),X0_54)
    | r1_tmap_1(sK3,X1_53,sK4,X0_54)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_53))
    | ~ m1_pre_topc(X0_53,sK3)
    | ~ m1_pre_topc(sK3,X2_53)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1296])).

cnf(c_2001,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK1)
    | r1_tmap_1(X1_53,X0_53,k3_tmap_1(X2_53,X0_53,sK3,X1_53,sK4),X0_54) != iProver_top
    | r1_tmap_1(sK3,X0_53,sK4,X0_54) = iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X1_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X2_53) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1324])).

cnf(c_2682,plain,
    ( r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_54) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_54) = iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2001])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_40,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_41,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_42,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_43,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_44,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_47,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_50,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_52,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1325,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK2))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1296])).

cnf(c_1375,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1325])).

cnf(c_1319,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ l1_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2250,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_2251,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2250])).

cnf(c_1320,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2335,plain,
    ( ~ m1_pre_topc(sK3,X0_53)
    | ~ l1_pre_topc(X0_53)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1320])).

cnf(c_2506,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2335])).

cnf(c_2507,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2506])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_470,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_5,c_7])).

cnf(c_1298,plain,
    ( v2_struct_0(X0_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v1_xboole_0(u1_struct_0(X0_53)) ),
    inference(subtyping,[status(esa)],[c_470])).

cnf(c_2579,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1298])).

cnf(c_2580,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2579])).

cnf(c_1310,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1986,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1310])).

cnf(c_1977,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1320])).

cnf(c_2839,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1986,c_1977])).

cnf(c_3560,plain,
    ( l1_pre_topc(X1_53) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_54) = iProver_top
    | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_54) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2682,c_40,c_41,c_42,c_43,c_44,c_47,c_50,c_52,c_1375,c_2251,c_2507,c_2580,c_2839])).

cnf(c_3561,plain,
    ( r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_54) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_54) = iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_3560])).

cnf(c_3578,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2073,c_3561])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_38,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_39,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_46,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_54,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1311,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1985,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1311])).

cnf(c_2028,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1985,c_1313])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1315,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1982,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1315])).

cnf(c_2084,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1982,c_1313])).

cnf(c_1327,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_2244,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_2361,plain,
    ( u1_struct_0(X0_53) = u1_struct_0(X0_53) ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_2366,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2361])).

cnf(c_17,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r2_hidden(X3,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_15,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_195,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_15])).

cnf(c_196,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_757,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_196,c_26])).

cnf(c_758,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_762,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_758,c_27])).

cnf(c_763,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_762])).

cnf(c_804,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_763,c_14])).

cnf(c_1297,plain,
    ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),X0_54)
    | ~ r1_tmap_1(X3_53,X1_53,sK4,X0_54)
    | ~ m1_pre_topc(X3_53,X2_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(X3_53))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X3_53) != u1_struct_0(sK3)
    | u1_struct_0(X1_53) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_804])).

cnf(c_2245,plain,
    ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,sK3,X0_53,sK4),X0_54)
    | ~ r1_tmap_1(sK3,X1_53,sK4,X0_54)
    | ~ m1_pre_topc(X0_53,sK3)
    | ~ m1_pre_topc(sK3,X2_53)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | u1_struct_0(X1_53) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_2344,plain,
    ( ~ r1_tmap_1(sK3,X0_53,sK4,X0_54)
    | r1_tmap_1(sK2,X0_53,k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4),X0_54)
    | ~ m1_pre_topc(sK3,X1_53)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X0_53)
    | u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2245])).

cnf(c_2696,plain,
    ( ~ r1_tmap_1(sK3,X0_53,sK4,X0_54)
    | r1_tmap_1(sK2,X0_53,k3_tmap_1(sK0,X0_53,sK3,sK2,sK4),X0_54)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK0)
    | u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2344])).

cnf(c_3421,plain,
    ( ~ r1_tmap_1(sK3,X0_53,sK4,sK6)
    | r1_tmap_1(sK2,X0_53,k3_tmap_1(sK0,X0_53,sK3,sK2,sK4),sK6)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
    | v2_struct_0(X0_53)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_53)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(X0_53)
    | ~ v2_pre_topc(sK0)
    | u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2696])).

cnf(c_3427,plain,
    ( u1_struct_0(X0_53) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(sK3,X0_53,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,X0_53,k3_tmap_1(sK0,X0_53,sK3,sK2,sK4),sK6) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3421])).

cnf(c_3429,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3427])).

cnf(c_3716,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3578,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_46,c_47,c_50,c_52,c_54,c_2028,c_2084,c_2244,c_2366,c_3429])).

cnf(c_3721,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1980,c_3716])).

cnf(c_3392,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1317])).

cnf(c_3393,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3392])).

cnf(c_3724,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3721,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_46,c_47,c_50,c_52,c_54,c_2028,c_2084,c_2244,c_2366,c_2507,c_2839,c_3393,c_3429,c_3578])).

cnf(c_3729,plain,
    ( l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1979,c_3724])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3729,c_2839,c_2507,c_47,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.15/1.08  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.08  
% 2.15/1.08  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.15/1.08  
% 2.15/1.08  ------  iProver source info
% 2.15/1.08  
% 2.15/1.08  git: date: 2020-06-30 10:37:57 +0100
% 2.15/1.08  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.15/1.08  git: non_committed_changes: false
% 2.15/1.08  git: last_make_outside_of_git: false
% 2.15/1.08  
% 2.15/1.08  ------ 
% 2.15/1.08  
% 2.15/1.08  ------ Input Options
% 2.15/1.08  
% 2.15/1.08  --out_options                           all
% 2.15/1.08  --tptp_safe_out                         true
% 2.15/1.08  --problem_path                          ""
% 2.15/1.08  --include_path                          ""
% 2.15/1.08  --clausifier                            res/vclausify_rel
% 2.15/1.08  --clausifier_options                    --mode clausify
% 2.15/1.08  --stdin                                 false
% 2.15/1.08  --stats_out                             all
% 2.15/1.08  
% 2.15/1.08  ------ General Options
% 2.15/1.08  
% 2.15/1.08  --fof                                   false
% 2.15/1.08  --time_out_real                         305.
% 2.15/1.08  --time_out_virtual                      -1.
% 2.15/1.08  --symbol_type_check                     false
% 2.15/1.08  --clausify_out                          false
% 2.15/1.08  --sig_cnt_out                           false
% 2.15/1.08  --trig_cnt_out                          false
% 2.15/1.08  --trig_cnt_out_tolerance                1.
% 2.15/1.08  --trig_cnt_out_sk_spl                   false
% 2.15/1.08  --abstr_cl_out                          false
% 2.15/1.08  
% 2.15/1.08  ------ Global Options
% 2.15/1.08  
% 2.15/1.08  --schedule                              default
% 2.15/1.08  --add_important_lit                     false
% 2.15/1.08  --prop_solver_per_cl                    1000
% 2.15/1.08  --min_unsat_core                        false
% 2.15/1.08  --soft_assumptions                      false
% 2.15/1.08  --soft_lemma_size                       3
% 2.15/1.08  --prop_impl_unit_size                   0
% 2.15/1.08  --prop_impl_unit                        []
% 2.15/1.08  --share_sel_clauses                     true
% 2.15/1.08  --reset_solvers                         false
% 2.15/1.08  --bc_imp_inh                            [conj_cone]
% 2.15/1.08  --conj_cone_tolerance                   3.
% 2.15/1.08  --extra_neg_conj                        none
% 2.15/1.08  --large_theory_mode                     true
% 2.15/1.08  --prolific_symb_bound                   200
% 2.15/1.08  --lt_threshold                          2000
% 2.15/1.08  --clause_weak_htbl                      true
% 2.15/1.08  --gc_record_bc_elim                     false
% 2.15/1.08  
% 2.15/1.08  ------ Preprocessing Options
% 2.15/1.08  
% 2.15/1.08  --preprocessing_flag                    true
% 2.15/1.08  --time_out_prep_mult                    0.1
% 2.15/1.08  --splitting_mode                        input
% 2.15/1.08  --splitting_grd                         true
% 2.15/1.08  --splitting_cvd                         false
% 2.15/1.08  --splitting_cvd_svl                     false
% 2.15/1.08  --splitting_nvd                         32
% 2.15/1.08  --sub_typing                            true
% 2.15/1.08  --prep_gs_sim                           true
% 2.15/1.08  --prep_unflatten                        true
% 2.15/1.08  --prep_res_sim                          true
% 2.15/1.08  --prep_upred                            true
% 2.15/1.08  --prep_sem_filter                       exhaustive
% 2.15/1.08  --prep_sem_filter_out                   false
% 2.15/1.08  --pred_elim                             true
% 2.15/1.08  --res_sim_input                         true
% 2.15/1.08  --eq_ax_congr_red                       true
% 2.15/1.08  --pure_diseq_elim                       true
% 2.15/1.08  --brand_transform                       false
% 2.15/1.08  --non_eq_to_eq                          false
% 2.15/1.08  --prep_def_merge                        true
% 2.15/1.08  --prep_def_merge_prop_impl              false
% 2.15/1.08  --prep_def_merge_mbd                    true
% 2.15/1.08  --prep_def_merge_tr_red                 false
% 2.15/1.08  --prep_def_merge_tr_cl                  false
% 2.15/1.08  --smt_preprocessing                     true
% 2.15/1.08  --smt_ac_axioms                         fast
% 2.15/1.08  --preprocessed_out                      false
% 2.15/1.08  --preprocessed_stats                    false
% 2.15/1.08  
% 2.15/1.08  ------ Abstraction refinement Options
% 2.15/1.08  
% 2.15/1.08  --abstr_ref                             []
% 2.15/1.08  --abstr_ref_prep                        false
% 2.15/1.08  --abstr_ref_until_sat                   false
% 2.15/1.08  --abstr_ref_sig_restrict                funpre
% 2.15/1.08  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/1.08  --abstr_ref_under                       []
% 2.15/1.08  
% 2.15/1.08  ------ SAT Options
% 2.15/1.08  
% 2.15/1.08  --sat_mode                              false
% 2.15/1.08  --sat_fm_restart_options                ""
% 2.15/1.08  --sat_gr_def                            false
% 2.15/1.08  --sat_epr_types                         true
% 2.15/1.08  --sat_non_cyclic_types                  false
% 2.15/1.08  --sat_finite_models                     false
% 2.15/1.08  --sat_fm_lemmas                         false
% 2.15/1.08  --sat_fm_prep                           false
% 2.15/1.08  --sat_fm_uc_incr                        true
% 2.15/1.08  --sat_out_model                         small
% 2.15/1.08  --sat_out_clauses                       false
% 2.15/1.08  
% 2.15/1.08  ------ QBF Options
% 2.15/1.08  
% 2.15/1.08  --qbf_mode                              false
% 2.15/1.08  --qbf_elim_univ                         false
% 2.15/1.08  --qbf_dom_inst                          none
% 2.15/1.08  --qbf_dom_pre_inst                      false
% 2.15/1.08  --qbf_sk_in                             false
% 2.15/1.08  --qbf_pred_elim                         true
% 2.15/1.08  --qbf_split                             512
% 2.15/1.08  
% 2.15/1.08  ------ BMC1 Options
% 2.15/1.08  
% 2.15/1.08  --bmc1_incremental                      false
% 2.15/1.08  --bmc1_axioms                           reachable_all
% 2.15/1.08  --bmc1_min_bound                        0
% 2.15/1.08  --bmc1_max_bound                        -1
% 2.15/1.08  --bmc1_max_bound_default                -1
% 2.15/1.08  --bmc1_symbol_reachability              true
% 2.15/1.08  --bmc1_property_lemmas                  false
% 2.15/1.08  --bmc1_k_induction                      false
% 2.15/1.08  --bmc1_non_equiv_states                 false
% 2.15/1.08  --bmc1_deadlock                         false
% 2.15/1.08  --bmc1_ucm                              false
% 2.15/1.08  --bmc1_add_unsat_core                   none
% 2.15/1.08  --bmc1_unsat_core_children              false
% 2.15/1.08  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/1.08  --bmc1_out_stat                         full
% 2.15/1.08  --bmc1_ground_init                      false
% 2.15/1.08  --bmc1_pre_inst_next_state              false
% 2.15/1.08  --bmc1_pre_inst_state                   false
% 2.15/1.08  --bmc1_pre_inst_reach_state             false
% 2.15/1.08  --bmc1_out_unsat_core                   false
% 2.15/1.08  --bmc1_aig_witness_out                  false
% 2.15/1.08  --bmc1_verbose                          false
% 2.15/1.08  --bmc1_dump_clauses_tptp                false
% 2.15/1.08  --bmc1_dump_unsat_core_tptp             false
% 2.15/1.08  --bmc1_dump_file                        -
% 2.15/1.08  --bmc1_ucm_expand_uc_limit              128
% 2.15/1.08  --bmc1_ucm_n_expand_iterations          6
% 2.15/1.08  --bmc1_ucm_extend_mode                  1
% 2.15/1.08  --bmc1_ucm_init_mode                    2
% 2.15/1.08  --bmc1_ucm_cone_mode                    none
% 2.15/1.08  --bmc1_ucm_reduced_relation_type        0
% 2.15/1.08  --bmc1_ucm_relax_model                  4
% 2.15/1.08  --bmc1_ucm_full_tr_after_sat            true
% 2.15/1.08  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/1.08  --bmc1_ucm_layered_model                none
% 2.15/1.08  --bmc1_ucm_max_lemma_size               10
% 2.15/1.08  
% 2.15/1.08  ------ AIG Options
% 2.15/1.08  
% 2.15/1.08  --aig_mode                              false
% 2.15/1.08  
% 2.15/1.08  ------ Instantiation Options
% 2.15/1.08  
% 2.15/1.08  --instantiation_flag                    true
% 2.15/1.08  --inst_sos_flag                         false
% 2.15/1.08  --inst_sos_phase                        true
% 2.15/1.08  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/1.08  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/1.08  --inst_lit_sel_side                     num_symb
% 2.15/1.08  --inst_solver_per_active                1400
% 2.15/1.08  --inst_solver_calls_frac                1.
% 2.15/1.08  --inst_passive_queue_type               priority_queues
% 2.15/1.08  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/1.08  --inst_passive_queues_freq              [25;2]
% 2.15/1.08  --inst_dismatching                      true
% 2.15/1.08  --inst_eager_unprocessed_to_passive     true
% 2.15/1.08  --inst_prop_sim_given                   true
% 2.15/1.08  --inst_prop_sim_new                     false
% 2.15/1.08  --inst_subs_new                         false
% 2.15/1.08  --inst_eq_res_simp                      false
% 2.15/1.08  --inst_subs_given                       false
% 2.15/1.08  --inst_orphan_elimination               true
% 2.15/1.08  --inst_learning_loop_flag               true
% 2.15/1.08  --inst_learning_start                   3000
% 2.15/1.08  --inst_learning_factor                  2
% 2.15/1.08  --inst_start_prop_sim_after_learn       3
% 2.15/1.08  --inst_sel_renew                        solver
% 2.15/1.08  --inst_lit_activity_flag                true
% 2.15/1.08  --inst_restr_to_given                   false
% 2.15/1.08  --inst_activity_threshold               500
% 2.15/1.08  --inst_out_proof                        true
% 2.15/1.08  
% 2.15/1.08  ------ Resolution Options
% 2.15/1.08  
% 2.15/1.08  --resolution_flag                       true
% 2.15/1.08  --res_lit_sel                           adaptive
% 2.15/1.08  --res_lit_sel_side                      none
% 2.15/1.08  --res_ordering                          kbo
% 2.15/1.08  --res_to_prop_solver                    active
% 2.15/1.08  --res_prop_simpl_new                    false
% 2.15/1.08  --res_prop_simpl_given                  true
% 2.15/1.08  --res_passive_queue_type                priority_queues
% 2.15/1.08  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/1.08  --res_passive_queues_freq               [15;5]
% 2.15/1.08  --res_forward_subs                      full
% 2.15/1.08  --res_backward_subs                     full
% 2.15/1.08  --res_forward_subs_resolution           true
% 2.15/1.08  --res_backward_subs_resolution          true
% 2.15/1.08  --res_orphan_elimination                true
% 2.15/1.08  --res_time_limit                        2.
% 2.15/1.08  --res_out_proof                         true
% 2.15/1.08  
% 2.15/1.08  ------ Superposition Options
% 2.15/1.08  
% 2.15/1.08  --superposition_flag                    true
% 2.15/1.08  --sup_passive_queue_type                priority_queues
% 2.15/1.08  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/1.08  --sup_passive_queues_freq               [8;1;4]
% 2.15/1.08  --demod_completeness_check              fast
% 2.15/1.08  --demod_use_ground                      true
% 2.15/1.08  --sup_to_prop_solver                    passive
% 2.15/1.08  --sup_prop_simpl_new                    true
% 2.15/1.08  --sup_prop_simpl_given                  true
% 2.15/1.08  --sup_fun_splitting                     false
% 2.15/1.08  --sup_smt_interval                      50000
% 2.15/1.08  
% 2.15/1.08  ------ Superposition Simplification Setup
% 2.15/1.08  
% 2.15/1.08  --sup_indices_passive                   []
% 2.15/1.08  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.08  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.08  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.08  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/1.08  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.08  --sup_full_bw                           [BwDemod]
% 2.15/1.08  --sup_immed_triv                        [TrivRules]
% 2.15/1.08  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.08  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.08  --sup_immed_bw_main                     []
% 2.15/1.08  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.08  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/1.08  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.08  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.08  
% 2.15/1.08  ------ Combination Options
% 2.15/1.08  
% 2.15/1.08  --comb_res_mult                         3
% 2.15/1.08  --comb_sup_mult                         2
% 2.15/1.08  --comb_inst_mult                        10
% 2.15/1.08  
% 2.15/1.08  ------ Debug Options
% 2.15/1.08  
% 2.15/1.08  --dbg_backtrace                         false
% 2.15/1.08  --dbg_dump_prop_clauses                 false
% 2.15/1.08  --dbg_dump_prop_clauses_file            -
% 2.15/1.08  --dbg_out_stat                          false
% 2.15/1.08  ------ Parsing...
% 2.15/1.08  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.15/1.08  
% 2.15/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.15/1.08  
% 2.15/1.08  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.15/1.08  
% 2.15/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.15/1.08  ------ Proving...
% 2.15/1.08  ------ Problem Properties 
% 2.15/1.08  
% 2.15/1.08  
% 2.15/1.08  clauses                                 29
% 2.15/1.08  conjectures                             17
% 2.15/1.08  EPR                                     18
% 2.15/1.08  Horn                                    25
% 2.15/1.08  unary                                   15
% 2.15/1.08  binary                                  3
% 2.15/1.08  lits                                    86
% 2.15/1.08  lits eq                                 4
% 2.15/1.08  fd_pure                                 0
% 2.15/1.08  fd_pseudo                               0
% 2.15/1.08  fd_cond                                 0
% 2.15/1.08  fd_pseudo_cond                          0
% 2.15/1.08  AC symbols                              0
% 2.15/1.08  
% 2.15/1.08  ------ Schedule dynamic 5 is on 
% 2.15/1.08  
% 2.15/1.08  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.15/1.08  
% 2.15/1.08  
% 2.15/1.08  ------ 
% 2.15/1.08  Current options:
% 2.15/1.08  ------ 
% 2.15/1.08  
% 2.15/1.08  ------ Input Options
% 2.15/1.08  
% 2.15/1.08  --out_options                           all
% 2.15/1.08  --tptp_safe_out                         true
% 2.15/1.08  --problem_path                          ""
% 2.15/1.08  --include_path                          ""
% 2.15/1.08  --clausifier                            res/vclausify_rel
% 2.15/1.08  --clausifier_options                    --mode clausify
% 2.15/1.08  --stdin                                 false
% 2.15/1.08  --stats_out                             all
% 2.15/1.08  
% 2.15/1.08  ------ General Options
% 2.15/1.08  
% 2.15/1.08  --fof                                   false
% 2.15/1.08  --time_out_real                         305.
% 2.15/1.08  --time_out_virtual                      -1.
% 2.15/1.08  --symbol_type_check                     false
% 2.15/1.08  --clausify_out                          false
% 2.15/1.08  --sig_cnt_out                           false
% 2.15/1.08  --trig_cnt_out                          false
% 2.15/1.08  --trig_cnt_out_tolerance                1.
% 2.15/1.08  --trig_cnt_out_sk_spl                   false
% 2.15/1.08  --abstr_cl_out                          false
% 2.15/1.08  
% 2.15/1.08  ------ Global Options
% 2.15/1.08  
% 2.15/1.08  --schedule                              default
% 2.15/1.08  --add_important_lit                     false
% 2.15/1.08  --prop_solver_per_cl                    1000
% 2.15/1.08  --min_unsat_core                        false
% 2.15/1.08  --soft_assumptions                      false
% 2.15/1.08  --soft_lemma_size                       3
% 2.15/1.08  --prop_impl_unit_size                   0
% 2.15/1.08  --prop_impl_unit                        []
% 2.15/1.08  --share_sel_clauses                     true
% 2.15/1.08  --reset_solvers                         false
% 2.15/1.08  --bc_imp_inh                            [conj_cone]
% 2.15/1.08  --conj_cone_tolerance                   3.
% 2.15/1.08  --extra_neg_conj                        none
% 2.15/1.08  --large_theory_mode                     true
% 2.15/1.08  --prolific_symb_bound                   200
% 2.15/1.08  --lt_threshold                          2000
% 2.15/1.08  --clause_weak_htbl                      true
% 2.15/1.08  --gc_record_bc_elim                     false
% 2.15/1.08  
% 2.15/1.08  ------ Preprocessing Options
% 2.15/1.08  
% 2.15/1.08  --preprocessing_flag                    true
% 2.15/1.08  --time_out_prep_mult                    0.1
% 2.15/1.08  --splitting_mode                        input
% 2.15/1.08  --splitting_grd                         true
% 2.15/1.08  --splitting_cvd                         false
% 2.15/1.08  --splitting_cvd_svl                     false
% 2.15/1.08  --splitting_nvd                         32
% 2.15/1.08  --sub_typing                            true
% 2.15/1.08  --prep_gs_sim                           true
% 2.15/1.08  --prep_unflatten                        true
% 2.15/1.08  --prep_res_sim                          true
% 2.15/1.08  --prep_upred                            true
% 2.15/1.08  --prep_sem_filter                       exhaustive
% 2.15/1.08  --prep_sem_filter_out                   false
% 2.15/1.08  --pred_elim                             true
% 2.15/1.08  --res_sim_input                         true
% 2.15/1.08  --eq_ax_congr_red                       true
% 2.15/1.08  --pure_diseq_elim                       true
% 2.15/1.08  --brand_transform                       false
% 2.15/1.08  --non_eq_to_eq                          false
% 2.15/1.08  --prep_def_merge                        true
% 2.15/1.08  --prep_def_merge_prop_impl              false
% 2.15/1.08  --prep_def_merge_mbd                    true
% 2.15/1.08  --prep_def_merge_tr_red                 false
% 2.15/1.08  --prep_def_merge_tr_cl                  false
% 2.15/1.08  --smt_preprocessing                     true
% 2.15/1.08  --smt_ac_axioms                         fast
% 2.15/1.08  --preprocessed_out                      false
% 2.15/1.08  --preprocessed_stats                    false
% 2.15/1.08  
% 2.15/1.08  ------ Abstraction refinement Options
% 2.15/1.08  
% 2.15/1.08  --abstr_ref                             []
% 2.15/1.08  --abstr_ref_prep                        false
% 2.15/1.08  --abstr_ref_until_sat                   false
% 2.15/1.08  --abstr_ref_sig_restrict                funpre
% 2.15/1.08  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/1.08  --abstr_ref_under                       []
% 2.15/1.08  
% 2.15/1.08  ------ SAT Options
% 2.15/1.08  
% 2.15/1.08  --sat_mode                              false
% 2.15/1.08  --sat_fm_restart_options                ""
% 2.15/1.08  --sat_gr_def                            false
% 2.15/1.08  --sat_epr_types                         true
% 2.15/1.08  --sat_non_cyclic_types                  false
% 2.15/1.08  --sat_finite_models                     false
% 2.15/1.08  --sat_fm_lemmas                         false
% 2.15/1.08  --sat_fm_prep                           false
% 2.15/1.08  --sat_fm_uc_incr                        true
% 2.15/1.08  --sat_out_model                         small
% 2.15/1.08  --sat_out_clauses                       false
% 2.15/1.08  
% 2.15/1.08  ------ QBF Options
% 2.15/1.08  
% 2.15/1.08  --qbf_mode                              false
% 2.15/1.08  --qbf_elim_univ                         false
% 2.15/1.08  --qbf_dom_inst                          none
% 2.15/1.08  --qbf_dom_pre_inst                      false
% 2.15/1.08  --qbf_sk_in                             false
% 2.15/1.08  --qbf_pred_elim                         true
% 2.15/1.08  --qbf_split                             512
% 2.15/1.08  
% 2.15/1.08  ------ BMC1 Options
% 2.15/1.08  
% 2.15/1.08  --bmc1_incremental                      false
% 2.15/1.08  --bmc1_axioms                           reachable_all
% 2.15/1.08  --bmc1_min_bound                        0
% 2.15/1.08  --bmc1_max_bound                        -1
% 2.15/1.08  --bmc1_max_bound_default                -1
% 2.15/1.08  --bmc1_symbol_reachability              true
% 2.15/1.08  --bmc1_property_lemmas                  false
% 2.15/1.08  --bmc1_k_induction                      false
% 2.15/1.08  --bmc1_non_equiv_states                 false
% 2.15/1.08  --bmc1_deadlock                         false
% 2.15/1.08  --bmc1_ucm                              false
% 2.15/1.08  --bmc1_add_unsat_core                   none
% 2.15/1.08  --bmc1_unsat_core_children              false
% 2.15/1.08  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/1.08  --bmc1_out_stat                         full
% 2.15/1.08  --bmc1_ground_init                      false
% 2.15/1.08  --bmc1_pre_inst_next_state              false
% 2.15/1.08  --bmc1_pre_inst_state                   false
% 2.15/1.08  --bmc1_pre_inst_reach_state             false
% 2.15/1.08  --bmc1_out_unsat_core                   false
% 2.15/1.08  --bmc1_aig_witness_out                  false
% 2.15/1.08  --bmc1_verbose                          false
% 2.15/1.08  --bmc1_dump_clauses_tptp                false
% 2.15/1.08  --bmc1_dump_unsat_core_tptp             false
% 2.15/1.08  --bmc1_dump_file                        -
% 2.15/1.08  --bmc1_ucm_expand_uc_limit              128
% 2.15/1.08  --bmc1_ucm_n_expand_iterations          6
% 2.15/1.08  --bmc1_ucm_extend_mode                  1
% 2.15/1.08  --bmc1_ucm_init_mode                    2
% 2.15/1.08  --bmc1_ucm_cone_mode                    none
% 2.15/1.08  --bmc1_ucm_reduced_relation_type        0
% 2.15/1.08  --bmc1_ucm_relax_model                  4
% 2.15/1.08  --bmc1_ucm_full_tr_after_sat            true
% 2.15/1.08  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/1.08  --bmc1_ucm_layered_model                none
% 2.15/1.08  --bmc1_ucm_max_lemma_size               10
% 2.15/1.08  
% 2.15/1.08  ------ AIG Options
% 2.15/1.08  
% 2.15/1.08  --aig_mode                              false
% 2.15/1.08  
% 2.15/1.08  ------ Instantiation Options
% 2.15/1.08  
% 2.15/1.08  --instantiation_flag                    true
% 2.15/1.08  --inst_sos_flag                         false
% 2.15/1.08  --inst_sos_phase                        true
% 2.15/1.08  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/1.08  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/1.08  --inst_lit_sel_side                     none
% 2.15/1.08  --inst_solver_per_active                1400
% 2.15/1.08  --inst_solver_calls_frac                1.
% 2.15/1.08  --inst_passive_queue_type               priority_queues
% 2.15/1.08  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/1.08  --inst_passive_queues_freq              [25;2]
% 2.15/1.08  --inst_dismatching                      true
% 2.15/1.08  --inst_eager_unprocessed_to_passive     true
% 2.15/1.08  --inst_prop_sim_given                   true
% 2.15/1.08  --inst_prop_sim_new                     false
% 2.15/1.08  --inst_subs_new                         false
% 2.15/1.08  --inst_eq_res_simp                      false
% 2.15/1.08  --inst_subs_given                       false
% 2.15/1.08  --inst_orphan_elimination               true
% 2.15/1.08  --inst_learning_loop_flag               true
% 2.15/1.08  --inst_learning_start                   3000
% 2.15/1.08  --inst_learning_factor                  2
% 2.15/1.08  --inst_start_prop_sim_after_learn       3
% 2.15/1.08  --inst_sel_renew                        solver
% 2.15/1.08  --inst_lit_activity_flag                true
% 2.15/1.08  --inst_restr_to_given                   false
% 2.15/1.08  --inst_activity_threshold               500
% 2.15/1.08  --inst_out_proof                        true
% 2.15/1.08  
% 2.15/1.08  ------ Resolution Options
% 2.15/1.08  
% 2.15/1.08  --resolution_flag                       false
% 2.15/1.08  --res_lit_sel                           adaptive
% 2.15/1.08  --res_lit_sel_side                      none
% 2.15/1.08  --res_ordering                          kbo
% 2.15/1.08  --res_to_prop_solver                    active
% 2.15/1.08  --res_prop_simpl_new                    false
% 2.15/1.08  --res_prop_simpl_given                  true
% 2.15/1.08  --res_passive_queue_type                priority_queues
% 2.15/1.08  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/1.08  --res_passive_queues_freq               [15;5]
% 2.15/1.08  --res_forward_subs                      full
% 2.15/1.08  --res_backward_subs                     full
% 2.15/1.08  --res_forward_subs_resolution           true
% 2.15/1.08  --res_backward_subs_resolution          true
% 2.15/1.08  --res_orphan_elimination                true
% 2.15/1.08  --res_time_limit                        2.
% 2.15/1.08  --res_out_proof                         true
% 2.15/1.08  
% 2.15/1.08  ------ Superposition Options
% 2.15/1.08  
% 2.15/1.08  --superposition_flag                    true
% 2.15/1.08  --sup_passive_queue_type                priority_queues
% 2.15/1.08  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/1.08  --sup_passive_queues_freq               [8;1;4]
% 2.15/1.08  --demod_completeness_check              fast
% 2.15/1.08  --demod_use_ground                      true
% 2.15/1.08  --sup_to_prop_solver                    passive
% 2.15/1.08  --sup_prop_simpl_new                    true
% 2.15/1.08  --sup_prop_simpl_given                  true
% 2.15/1.08  --sup_fun_splitting                     false
% 2.15/1.08  --sup_smt_interval                      50000
% 2.15/1.08  
% 2.15/1.08  ------ Superposition Simplification Setup
% 2.15/1.08  
% 2.15/1.08  --sup_indices_passive                   []
% 2.15/1.08  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.08  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.08  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.08  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/1.08  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.08  --sup_full_bw                           [BwDemod]
% 2.15/1.08  --sup_immed_triv                        [TrivRules]
% 2.15/1.08  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.08  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.08  --sup_immed_bw_main                     []
% 2.15/1.08  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.08  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/1.08  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.08  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.08  
% 2.15/1.08  ------ Combination Options
% 2.15/1.08  
% 2.15/1.08  --comb_res_mult                         3
% 2.15/1.08  --comb_sup_mult                         2
% 2.15/1.08  --comb_inst_mult                        10
% 2.15/1.08  
% 2.15/1.08  ------ Debug Options
% 2.15/1.08  
% 2.15/1.08  --dbg_backtrace                         false
% 2.15/1.08  --dbg_dump_prop_clauses                 false
% 2.15/1.08  --dbg_dump_prop_clauses_file            -
% 2.15/1.08  --dbg_out_stat                          false
% 2.15/1.08  
% 2.15/1.08  
% 2.15/1.08  
% 2.15/1.08  
% 2.15/1.08  ------ Proving...
% 2.15/1.08  
% 2.15/1.08  
% 2.15/1.08  % SZS status Theorem for theBenchmark.p
% 2.15/1.08  
% 2.15/1.08  % SZS output start CNFRefutation for theBenchmark.p
% 2.15/1.08  
% 2.15/1.08  fof(f8,axiom,(
% 2.15/1.08    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.15/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.08  
% 2.15/1.08  fof(f25,plain,(
% 2.15/1.08    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.15/1.08    inference(ennf_transformation,[],[f8])).
% 2.15/1.08  
% 2.15/1.08  fof(f61,plain,(
% 2.15/1.08    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.15/1.08    inference(cnf_transformation,[],[f25])).
% 2.15/1.08  
% 2.15/1.08  fof(f9,axiom,(
% 2.15/1.08    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 2.15/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.08  
% 2.15/1.08  fof(f26,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.15/1.08    inference(ennf_transformation,[],[f9])).
% 2.15/1.08  
% 2.15/1.08  fof(f62,plain,(
% 2.15/1.08    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.15/1.08    inference(cnf_transformation,[],[f26])).
% 2.15/1.08  
% 2.15/1.08  fof(f13,conjecture,(
% 2.15/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 2.15/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.08  
% 2.15/1.08  fof(f14,negated_conjecture,(
% 2.15/1.08    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 2.15/1.08    inference(negated_conjecture,[],[f13])).
% 2.15/1.08  
% 2.15/1.08  fof(f33,plain,(
% 2.15/1.08    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.15/1.08    inference(ennf_transformation,[],[f14])).
% 2.15/1.08  
% 2.15/1.08  fof(f34,plain,(
% 2.15/1.08    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.15/1.08    inference(flattening,[],[f33])).
% 2.15/1.08  
% 2.15/1.08  fof(f39,plain,(
% 2.15/1.08    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.15/1.08    inference(nnf_transformation,[],[f34])).
% 2.15/1.08  
% 2.15/1.08  fof(f40,plain,(
% 2.15/1.08    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.15/1.08    inference(flattening,[],[f39])).
% 2.15/1.08  
% 2.15/1.08  fof(f47,plain,(
% 2.15/1.08    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) | r1_tmap_1(X3,X1,X4,X5)) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 2.15/1.08    introduced(choice_axiom,[])).
% 2.15/1.08  
% 2.15/1.08  fof(f46,plain,(
% 2.15/1.08    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,sK5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 2.15/1.08    introduced(choice_axiom,[])).
% 2.15/1.08  
% 2.15/1.08  fof(f45,plain,(
% 2.15/1.08    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) | ~r1_tmap_1(X3,X1,sK4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) | r1_tmap_1(X3,X1,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.15/1.08    introduced(choice_axiom,[])).
% 2.15/1.08  
% 2.15/1.08  fof(f44,plain,(
% 2.15/1.08    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) | ~r1_tmap_1(sK3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) | r1_tmap_1(sK3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(X2,sK3) & v1_tsep_1(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.15/1.08    introduced(choice_axiom,[])).
% 2.15/1.08  
% 2.15/1.08  fof(f43,plain,(
% 2.15/1.08    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & v1_tsep_1(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.15/1.08    introduced(choice_axiom,[])).
% 2.15/1.08  
% 2.15/1.08  fof(f42,plain,(
% 2.15/1.08    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.15/1.08    introduced(choice_axiom,[])).
% 2.15/1.08  
% 2.15/1.08  fof(f41,plain,(
% 2.15/1.08    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.15/1.08    introduced(choice_axiom,[])).
% 2.15/1.08  
% 2.15/1.08  fof(f48,plain,(
% 2.15/1.08    (((((((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.15/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f40,f47,f46,f45,f44,f43,f42,f41])).
% 2.15/1.08  
% 2.15/1.08  fof(f85,plain,(
% 2.15/1.08    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f84,plain,(
% 2.15/1.08    sK5 = sK6),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f78,plain,(
% 2.15/1.08    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f1,axiom,(
% 2.15/1.08    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.15/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.08  
% 2.15/1.08  fof(f15,plain,(
% 2.15/1.08    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.15/1.08    inference(ennf_transformation,[],[f1])).
% 2.15/1.08  
% 2.15/1.08  fof(f35,plain,(
% 2.15/1.08    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.15/1.08    inference(nnf_transformation,[],[f15])).
% 2.15/1.08  
% 2.15/1.08  fof(f49,plain,(
% 2.15/1.08    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.15/1.08    inference(cnf_transformation,[],[f35])).
% 2.15/1.08  
% 2.15/1.08  fof(f12,axiom,(
% 2.15/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.15/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.08  
% 2.15/1.08  fof(f31,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.15/1.08    inference(ennf_transformation,[],[f12])).
% 2.15/1.08  
% 2.15/1.08  fof(f32,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.15/1.08    inference(flattening,[],[f31])).
% 2.15/1.08  
% 2.15/1.08  fof(f38,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.15/1.08    inference(nnf_transformation,[],[f32])).
% 2.15/1.08  
% 2.15/1.08  fof(f66,plain,(
% 2.15/1.08    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.08    inference(cnf_transformation,[],[f38])).
% 2.15/1.08  
% 2.15/1.08  fof(f91,plain,(
% 2.15/1.08    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.08    inference(equality_resolution,[],[f66])).
% 2.15/1.08  
% 2.15/1.08  fof(f6,axiom,(
% 2.15/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.15/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.08  
% 2.15/1.08  fof(f22,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.15/1.08    inference(ennf_transformation,[],[f6])).
% 2.15/1.08  
% 2.15/1.08  fof(f23,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.15/1.08    inference(flattening,[],[f22])).
% 2.15/1.08  
% 2.15/1.08  fof(f36,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.15/1.08    inference(nnf_transformation,[],[f23])).
% 2.15/1.08  
% 2.15/1.08  fof(f37,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.15/1.08    inference(flattening,[],[f36])).
% 2.15/1.08  
% 2.15/1.08  fof(f57,plain,(
% 2.15/1.08    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/1.08    inference(cnf_transformation,[],[f37])).
% 2.15/1.08  
% 2.15/1.08  fof(f89,plain,(
% 2.15/1.08    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/1.08    inference(equality_resolution,[],[f57])).
% 2.15/1.08  
% 2.15/1.08  fof(f7,axiom,(
% 2.15/1.08    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.15/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.08  
% 2.15/1.08  fof(f24,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.15/1.08    inference(ennf_transformation,[],[f7])).
% 2.15/1.08  
% 2.15/1.08  fof(f60,plain,(
% 2.15/1.08    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.15/1.08    inference(cnf_transformation,[],[f24])).
% 2.15/1.08  
% 2.15/1.08  fof(f80,plain,(
% 2.15/1.08    v1_tsep_1(sK2,sK3)),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f81,plain,(
% 2.15/1.08    m1_pre_topc(sK2,sK3)),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f75,plain,(
% 2.15/1.08    ~v2_struct_0(sK3)),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f2,axiom,(
% 2.15/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.15/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.08  
% 2.15/1.08  fof(f16,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.15/1.08    inference(ennf_transformation,[],[f2])).
% 2.15/1.08  
% 2.15/1.08  fof(f17,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.15/1.08    inference(flattening,[],[f16])).
% 2.15/1.08  
% 2.15/1.08  fof(f53,plain,(
% 2.15/1.08    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/1.08    inference(cnf_transformation,[],[f17])).
% 2.15/1.08  
% 2.15/1.08  fof(f4,axiom,(
% 2.15/1.08    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.15/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.08  
% 2.15/1.08  fof(f19,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.15/1.08    inference(ennf_transformation,[],[f4])).
% 2.15/1.08  
% 2.15/1.08  fof(f55,plain,(
% 2.15/1.08    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.15/1.08    inference(cnf_transformation,[],[f19])).
% 2.15/1.08  
% 2.15/1.08  fof(f10,axiom,(
% 2.15/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.15/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.08  
% 2.15/1.08  fof(f27,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.15/1.08    inference(ennf_transformation,[],[f10])).
% 2.15/1.08  
% 2.15/1.08  fof(f28,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.15/1.08    inference(flattening,[],[f27])).
% 2.15/1.08  
% 2.15/1.08  fof(f63,plain,(
% 2.15/1.08    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.15/1.08    inference(cnf_transformation,[],[f28])).
% 2.15/1.08  
% 2.15/1.08  fof(f77,plain,(
% 2.15/1.08    v1_funct_1(sK4)),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f69,plain,(
% 2.15/1.08    l1_pre_topc(sK0)),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f70,plain,(
% 2.15/1.08    ~v2_struct_0(sK1)),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f71,plain,(
% 2.15/1.08    v2_pre_topc(sK1)),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f72,plain,(
% 2.15/1.08    l1_pre_topc(sK1)),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f73,plain,(
% 2.15/1.08    ~v2_struct_0(sK2)),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f76,plain,(
% 2.15/1.08    m1_pre_topc(sK3,sK0)),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f79,plain,(
% 2.15/1.08    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f3,axiom,(
% 2.15/1.08    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.15/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.08  
% 2.15/1.08  fof(f18,plain,(
% 2.15/1.08    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.15/1.08    inference(ennf_transformation,[],[f3])).
% 2.15/1.08  
% 2.15/1.08  fof(f54,plain,(
% 2.15/1.08    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.15/1.08    inference(cnf_transformation,[],[f18])).
% 2.15/1.08  
% 2.15/1.08  fof(f5,axiom,(
% 2.15/1.08    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.15/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.08  
% 2.15/1.08  fof(f20,plain,(
% 2.15/1.08    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.15/1.08    inference(ennf_transformation,[],[f5])).
% 2.15/1.08  
% 2.15/1.08  fof(f21,plain,(
% 2.15/1.08    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.15/1.08    inference(flattening,[],[f20])).
% 2.15/1.08  
% 2.15/1.08  fof(f56,plain,(
% 2.15/1.08    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.15/1.08    inference(cnf_transformation,[],[f21])).
% 2.15/1.08  
% 2.15/1.08  fof(f67,plain,(
% 2.15/1.08    ~v2_struct_0(sK0)),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f68,plain,(
% 2.15/1.08    v2_pre_topc(sK0)),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f83,plain,(
% 2.15/1.08    m1_subset_1(sK6,u1_struct_0(sK2))),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f82,plain,(
% 2.15/1.08    m1_subset_1(sK5,u1_struct_0(sK3))),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f86,plain,(
% 2.15/1.08    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 2.15/1.08    inference(cnf_transformation,[],[f48])).
% 2.15/1.08  
% 2.15/1.08  fof(f65,plain,(
% 2.15/1.08    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.08    inference(cnf_transformation,[],[f38])).
% 2.15/1.08  
% 2.15/1.08  fof(f92,plain,(
% 2.15/1.08    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.08    inference(equality_resolution,[],[f65])).
% 2.15/1.08  
% 2.15/1.08  fof(f11,axiom,(
% 2.15/1.08    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 2.15/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.15/1.08  
% 2.15/1.08  fof(f29,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.15/1.08    inference(ennf_transformation,[],[f11])).
% 2.15/1.08  
% 2.15/1.08  fof(f30,plain,(
% 2.15/1.08    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.15/1.08    inference(flattening,[],[f29])).
% 2.15/1.08  
% 2.15/1.08  fof(f64,plain,(
% 2.15/1.08    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.08    inference(cnf_transformation,[],[f30])).
% 2.15/1.08  
% 2.15/1.08  fof(f90,plain,(
% 2.15/1.08    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.15/1.08    inference(equality_resolution,[],[f64])).
% 2.15/1.08  
% 2.15/1.08  cnf(c_12,plain,
% 2.15/1.08      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.15/1.08      inference(cnf_transformation,[],[f61]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1318,plain,
% 2.15/1.08      ( m1_pre_topc(X0_53,X0_53) | ~ l1_pre_topc(X0_53) ),
% 2.15/1.08      inference(subtyping,[status(esa)],[c_12]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1979,plain,
% 2.15/1.08      ( m1_pre_topc(X0_53,X0_53) = iProver_top
% 2.15/1.08      | l1_pre_topc(X0_53) != iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_1318]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_13,plain,
% 2.15/1.08      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.15/1.08      | ~ m1_pre_topc(X0,X1)
% 2.15/1.08      | ~ l1_pre_topc(X1) ),
% 2.15/1.08      inference(cnf_transformation,[],[f62]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1317,plain,
% 2.15/1.08      ( r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53))
% 2.15/1.08      | ~ m1_pre_topc(X0_53,X1_53)
% 2.15/1.08      | ~ l1_pre_topc(X1_53) ),
% 2.15/1.08      inference(subtyping,[status(esa)],[c_13]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1980,plain,
% 2.15/1.08      ( r1_tarski(u1_struct_0(X0_53),u1_struct_0(X1_53)) = iProver_top
% 2.15/1.08      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.15/1.08      | l1_pre_topc(X1_53) != iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_1317]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_19,negated_conjecture,
% 2.15/1.08      ( r1_tmap_1(sK3,sK1,sK4,sK5)
% 2.15/1.08      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 2.15/1.08      inference(cnf_transformation,[],[f85]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1314,negated_conjecture,
% 2.15/1.08      ( r1_tmap_1(sK3,sK1,sK4,sK5)
% 2.15/1.08      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 2.15/1.08      inference(subtyping,[status(esa)],[c_19]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1983,plain,
% 2.15/1.08      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 2.15/1.08      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_1314]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_20,negated_conjecture,
% 2.15/1.08      ( sK5 = sK6 ),
% 2.15/1.08      inference(cnf_transformation,[],[f84]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1313,negated_conjecture,
% 2.15/1.08      ( sK5 = sK6 ),
% 2.15/1.08      inference(subtyping,[status(esa)],[c_20]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2073,plain,
% 2.15/1.08      ( r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
% 2.15/1.08      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 2.15/1.08      inference(light_normalisation,[status(thm)],[c_1983,c_1313]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_26,negated_conjecture,
% 2.15/1.08      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 2.15/1.08      inference(cnf_transformation,[],[f78]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_3,plain,
% 2.15/1.08      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.15/1.08      inference(cnf_transformation,[],[f49]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_16,plain,
% 2.15/1.08      ( r1_tmap_1(X0,X1,X2,X3)
% 2.15/1.08      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.15/1.08      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.15/1.08      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.15/1.08      | ~ v3_pre_topc(X6,X0)
% 2.15/1.08      | ~ m1_pre_topc(X0,X5)
% 2.15/1.08      | ~ m1_pre_topc(X4,X5)
% 2.15/1.08      | ~ m1_pre_topc(X4,X0)
% 2.15/1.08      | ~ r2_hidden(X3,X6)
% 2.15/1.08      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.15/1.08      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.15/1.08      | ~ v1_funct_1(X2)
% 2.15/1.08      | v2_struct_0(X5)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X4)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | ~ l1_pre_topc(X5)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X5)
% 2.15/1.08      | ~ v2_pre_topc(X1) ),
% 2.15/1.08      inference(cnf_transformation,[],[f91]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_10,plain,
% 2.15/1.08      ( ~ v1_tsep_1(X0,X1)
% 2.15/1.08      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.15/1.08      | ~ m1_pre_topc(X0,X1)
% 2.15/1.08      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X1) ),
% 2.15/1.08      inference(cnf_transformation,[],[f89]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_11,plain,
% 2.15/1.08      ( ~ m1_pre_topc(X0,X1)
% 2.15/1.08      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.15/1.08      | ~ l1_pre_topc(X1) ),
% 2.15/1.08      inference(cnf_transformation,[],[f60]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_206,plain,
% 2.15/1.08      ( ~ m1_pre_topc(X0,X1)
% 2.15/1.08      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.15/1.08      | ~ v1_tsep_1(X0,X1)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X1) ),
% 2.15/1.08      inference(global_propositional_subsumption,
% 2.15/1.08                [status(thm)],
% 2.15/1.08                [c_10,c_11]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_207,plain,
% 2.15/1.08      ( ~ v1_tsep_1(X0,X1)
% 2.15/1.08      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.15/1.08      | ~ m1_pre_topc(X0,X1)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X1) ),
% 2.15/1.08      inference(renaming,[status(thm)],[c_206]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_24,negated_conjecture,
% 2.15/1.08      ( v1_tsep_1(sK2,sK3) ),
% 2.15/1.08      inference(cnf_transformation,[],[f80]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_489,plain,
% 2.15/1.08      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.15/1.08      | ~ m1_pre_topc(X0,X1)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | sK3 != X1
% 2.15/1.08      | sK2 != X0 ),
% 2.15/1.08      inference(resolution_lifted,[status(thm)],[c_207,c_24]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_490,plain,
% 2.15/1.08      ( v3_pre_topc(u1_struct_0(sK2),sK3)
% 2.15/1.08      | ~ m1_pre_topc(sK2,sK3)
% 2.15/1.08      | ~ l1_pre_topc(sK3)
% 2.15/1.08      | ~ v2_pre_topc(sK3) ),
% 2.15/1.08      inference(unflattening,[status(thm)],[c_489]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_23,negated_conjecture,
% 2.15/1.08      ( m1_pre_topc(sK2,sK3) ),
% 2.15/1.08      inference(cnf_transformation,[],[f81]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_492,plain,
% 2.15/1.08      ( v3_pre_topc(u1_struct_0(sK2),sK3)
% 2.15/1.08      | ~ l1_pre_topc(sK3)
% 2.15/1.08      | ~ v2_pre_topc(sK3) ),
% 2.15/1.08      inference(global_propositional_subsumption,
% 2.15/1.08                [status(thm)],
% 2.15/1.08                [c_490,c_23]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_510,plain,
% 2.15/1.08      ( r1_tmap_1(X0,X1,X2,X3)
% 2.15/1.08      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.15/1.08      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.15/1.08      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.15/1.08      | ~ m1_pre_topc(X4,X0)
% 2.15/1.08      | ~ m1_pre_topc(X4,X5)
% 2.15/1.08      | ~ m1_pre_topc(X0,X5)
% 2.15/1.08      | ~ r2_hidden(X3,X6)
% 2.15/1.08      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.15/1.08      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.15/1.08      | ~ v1_funct_1(X2)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(X5)
% 2.15/1.08      | v2_struct_0(X4)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X5)
% 2.15/1.08      | ~ l1_pre_topc(sK3)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X5)
% 2.15/1.08      | ~ v2_pre_topc(sK3)
% 2.15/1.08      | u1_struct_0(sK2) != X6
% 2.15/1.08      | sK3 != X0 ),
% 2.15/1.08      inference(resolution_lifted,[status(thm)],[c_16,c_492]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_511,plain,
% 2.15/1.08      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,X3),X4)
% 2.15/1.08      | r1_tmap_1(sK3,X1,X3,X4)
% 2.15/1.08      | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
% 2.15/1.08      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.15/1.08      | ~ m1_pre_topc(X0,X2)
% 2.15/1.08      | ~ m1_pre_topc(X0,sK3)
% 2.15/1.08      | ~ m1_pre_topc(sK3,X2)
% 2.15/1.08      | ~ r2_hidden(X4,u1_struct_0(sK2))
% 2.15/1.08      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.08      | ~ v1_funct_1(X3)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X2)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(sK3)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X2)
% 2.15/1.08      | ~ l1_pre_topc(sK3)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X2)
% 2.15/1.08      | ~ v2_pre_topc(sK3) ),
% 2.15/1.08      inference(unflattening,[status(thm)],[c_510]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_29,negated_conjecture,
% 2.15/1.08      ( ~ v2_struct_0(sK3) ),
% 2.15/1.08      inference(cnf_transformation,[],[f75]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_515,plain,
% 2.15/1.08      ( v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(X2)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | ~ v1_funct_1(X3)
% 2.15/1.08      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.15/1.08      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.15/1.08      | ~ r2_hidden(X4,u1_struct_0(sK2))
% 2.15/1.08      | ~ m1_pre_topc(sK3,X2)
% 2.15/1.08      | ~ m1_pre_topc(X0,sK3)
% 2.15/1.08      | ~ m1_pre_topc(X0,X2)
% 2.15/1.08      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.15/1.08      | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
% 2.15/1.08      | r1_tmap_1(sK3,X1,X3,X4)
% 2.15/1.08      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,X3),X4)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X2)
% 2.15/1.08      | ~ l1_pre_topc(sK3)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X2)
% 2.15/1.08      | ~ v2_pre_topc(sK3) ),
% 2.15/1.08      inference(global_propositional_subsumption,
% 2.15/1.08                [status(thm)],
% 2.15/1.08                [c_511,c_29]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_516,plain,
% 2.15/1.08      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,X3),X4)
% 2.15/1.08      | r1_tmap_1(sK3,X1,X3,X4)
% 2.15/1.08      | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
% 2.15/1.08      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.15/1.08      | ~ m1_pre_topc(X0,X2)
% 2.15/1.08      | ~ m1_pre_topc(X0,sK3)
% 2.15/1.08      | ~ m1_pre_topc(sK3,X2)
% 2.15/1.08      | ~ r2_hidden(X4,u1_struct_0(sK2))
% 2.15/1.08      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.08      | ~ v1_funct_1(X3)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(X2)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X2)
% 2.15/1.08      | ~ l1_pre_topc(sK3)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X2)
% 2.15/1.08      | ~ v2_pre_topc(sK3) ),
% 2.15/1.08      inference(renaming,[status(thm)],[c_515]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_4,plain,
% 2.15/1.08      ( ~ m1_pre_topc(X0,X1)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | v2_pre_topc(X0) ),
% 2.15/1.08      inference(cnf_transformation,[],[f53]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_6,plain,
% 2.15/1.08      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.15/1.08      inference(cnf_transformation,[],[f55]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_14,plain,
% 2.15/1.08      ( ~ m1_pre_topc(X0,X1)
% 2.15/1.08      | ~ m1_pre_topc(X2,X0)
% 2.15/1.08      | m1_pre_topc(X2,X1)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X1) ),
% 2.15/1.08      inference(cnf_transformation,[],[f63]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_565,plain,
% 2.15/1.08      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,X3),X4)
% 2.15/1.08      | r1_tmap_1(sK3,X1,X3,X4)
% 2.15/1.08      | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
% 2.15/1.08      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.15/1.08      | ~ m1_pre_topc(X0,sK3)
% 2.15/1.08      | ~ m1_pre_topc(sK3,X2)
% 2.15/1.08      | ~ r2_hidden(X4,u1_struct_0(sK2))
% 2.15/1.08      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.08      | ~ v1_funct_1(X3)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(X2)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X2)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X2) ),
% 2.15/1.08      inference(forward_subsumption_resolution,
% 2.15/1.08                [status(thm)],
% 2.15/1.08                [c_516,c_4,c_6,c_14]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_639,plain,
% 2.15/1.08      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,X3),X4)
% 2.15/1.08      | r1_tmap_1(sK3,X1,X3,X4)
% 2.15/1.08      | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
% 2.15/1.08      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.15/1.08      | ~ m1_pre_topc(X0,sK3)
% 2.15/1.08      | ~ m1_pre_topc(sK3,X2)
% 2.15/1.08      | ~ m1_subset_1(X5,X6)
% 2.15/1.08      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.08      | ~ v1_funct_1(X3)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(X2)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | ~ l1_pre_topc(X2)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X2)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | v1_xboole_0(X6)
% 2.15/1.08      | X4 != X5
% 2.15/1.08      | u1_struct_0(sK2) != X6 ),
% 2.15/1.08      inference(resolution_lifted,[status(thm)],[c_3,c_565]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_640,plain,
% 2.15/1.08      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,X3),X4)
% 2.15/1.08      | r1_tmap_1(sK3,X1,X3,X4)
% 2.15/1.08      | ~ v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
% 2.15/1.08      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.15/1.08      | ~ m1_pre_topc(X0,sK3)
% 2.15/1.08      | ~ m1_pre_topc(sK3,X2)
% 2.15/1.08      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(sK2))
% 2.15/1.08      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.08      | ~ v1_funct_1(X3)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(X2)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X2)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X2)
% 2.15/1.08      | v1_xboole_0(u1_struct_0(sK2)) ),
% 2.15/1.08      inference(unflattening,[status(thm)],[c_639]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_881,plain,
% 2.15/1.08      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,X3),X4)
% 2.15/1.08      | r1_tmap_1(sK3,X1,X3,X4)
% 2.15/1.08      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.15/1.08      | ~ m1_pre_topc(X0,sK3)
% 2.15/1.08      | ~ m1_pre_topc(sK3,X2)
% 2.15/1.08      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(sK2))
% 2.15/1.08      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.08      | ~ v1_funct_1(X3)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(X2)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X2)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X2)
% 2.15/1.08      | v1_xboole_0(u1_struct_0(sK2))
% 2.15/1.08      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.15/1.08      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.15/1.08      | sK4 != X3 ),
% 2.15/1.08      inference(resolution_lifted,[status(thm)],[c_26,c_640]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_882,plain,
% 2.15/1.08      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),X3)
% 2.15/1.08      | r1_tmap_1(sK3,X1,sK4,X3)
% 2.15/1.08      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.15/1.08      | ~ m1_pre_topc(X0,sK3)
% 2.15/1.08      | ~ m1_pre_topc(sK3,X2)
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 2.15/1.08      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.15/1.08      | ~ v1_funct_1(sK4)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(X2)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X2)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X2)
% 2.15/1.08      | v1_xboole_0(u1_struct_0(sK2))
% 2.15/1.08      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.15/1.08      inference(unflattening,[status(thm)],[c_881]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_27,negated_conjecture,
% 2.15/1.08      ( v1_funct_1(sK4) ),
% 2.15/1.08      inference(cnf_transformation,[],[f77]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_886,plain,
% 2.15/1.08      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.15/1.08      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.15/1.08      | ~ m1_pre_topc(sK3,X2)
% 2.15/1.08      | ~ m1_pre_topc(X0,sK3)
% 2.15/1.08      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.15/1.08      | r1_tmap_1(sK3,X1,sK4,X3)
% 2.15/1.08      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),X3)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(X2)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X2)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X2)
% 2.15/1.08      | v1_xboole_0(u1_struct_0(sK2))
% 2.15/1.08      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.15/1.08      inference(global_propositional_subsumption,
% 2.15/1.08                [status(thm)],
% 2.15/1.08                [c_882,c_27]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_887,plain,
% 2.15/1.08      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),X3)
% 2.15/1.08      | r1_tmap_1(sK3,X1,sK4,X3)
% 2.15/1.08      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.15/1.08      | ~ m1_pre_topc(X0,sK3)
% 2.15/1.08      | ~ m1_pre_topc(sK3,X2)
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 2.15/1.08      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(X2)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X2)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X2)
% 2.15/1.08      | v1_xboole_0(u1_struct_0(sK2))
% 2.15/1.08      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.15/1.08      inference(renaming,[status(thm)],[c_886]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1296,plain,
% 2.15/1.08      ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,sK3,X0_53,sK4),X0_54)
% 2.15/1.08      | r1_tmap_1(sK3,X1_53,sK4,X0_54)
% 2.15/1.08      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_53))
% 2.15/1.08      | ~ m1_pre_topc(X0_53,sK3)
% 2.15/1.08      | ~ m1_pre_topc(sK3,X2_53)
% 2.15/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.15/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 2.15/1.08      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 2.15/1.08      | v2_struct_0(X1_53)
% 2.15/1.08      | v2_struct_0(X0_53)
% 2.15/1.08      | v2_struct_0(X2_53)
% 2.15/1.08      | ~ l1_pre_topc(X1_53)
% 2.15/1.08      | ~ l1_pre_topc(X2_53)
% 2.15/1.08      | ~ v2_pre_topc(X1_53)
% 2.15/1.08      | ~ v2_pre_topc(X2_53)
% 2.15/1.08      | v1_xboole_0(u1_struct_0(sK2))
% 2.15/1.08      | u1_struct_0(X1_53) != u1_struct_0(sK1) ),
% 2.15/1.08      inference(subtyping,[status(esa)],[c_887]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1324,plain,
% 2.15/1.08      ( ~ r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,sK3,X0_53,sK4),X0_54)
% 2.15/1.08      | r1_tmap_1(sK3,X1_53,sK4,X0_54)
% 2.15/1.08      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_53))
% 2.15/1.08      | ~ m1_pre_topc(X0_53,sK3)
% 2.15/1.08      | ~ m1_pre_topc(sK3,X2_53)
% 2.15/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.15/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 2.15/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 2.15/1.08      | v2_struct_0(X1_53)
% 2.15/1.08      | v2_struct_0(X0_53)
% 2.15/1.08      | v2_struct_0(X2_53)
% 2.15/1.08      | ~ l1_pre_topc(X1_53)
% 2.15/1.08      | ~ l1_pre_topc(X2_53)
% 2.15/1.08      | ~ v2_pre_topc(X1_53)
% 2.15/1.08      | ~ v2_pre_topc(X2_53)
% 2.15/1.08      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 2.15/1.08      | ~ sP0_iProver_split ),
% 2.15/1.08      inference(splitting,
% 2.15/1.08                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.15/1.08                [c_1296]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2001,plain,
% 2.15/1.08      ( u1_struct_0(X0_53) != u1_struct_0(sK1)
% 2.15/1.08      | r1_tmap_1(X1_53,X0_53,k3_tmap_1(X2_53,X0_53,sK3,X1_53,sK4),X0_54) != iProver_top
% 2.15/1.08      | r1_tmap_1(sK3,X0_53,sK4,X0_54) = iProver_top
% 2.15/1.08      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X1_53)) != iProver_top
% 2.15/1.08      | m1_pre_topc(X1_53,sK3) != iProver_top
% 2.15/1.08      | m1_pre_topc(sK3,X2_53) != iProver_top
% 2.15/1.08      | m1_subset_1(X0_54,u1_struct_0(X1_53)) != iProver_top
% 2.15/1.08      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 2.15/1.08      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 2.15/1.08      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
% 2.15/1.08      | v2_struct_0(X0_53) = iProver_top
% 2.15/1.08      | v2_struct_0(X1_53) = iProver_top
% 2.15/1.08      | v2_struct_0(X2_53) = iProver_top
% 2.15/1.08      | l1_pre_topc(X0_53) != iProver_top
% 2.15/1.08      | l1_pre_topc(X2_53) != iProver_top
% 2.15/1.08      | v2_pre_topc(X0_53) != iProver_top
% 2.15/1.08      | v2_pre_topc(X2_53) != iProver_top
% 2.15/1.08      | sP0_iProver_split != iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_1324]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2682,plain,
% 2.15/1.08      ( r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_54) != iProver_top
% 2.15/1.08      | r1_tmap_1(sK3,sK1,sK4,X0_54) = iProver_top
% 2.15/1.08      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
% 2.15/1.08      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.15/1.08      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.15/1.08      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.15/1.08      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 2.15/1.08      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 2.15/1.08      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.15/1.08      | v2_struct_0(X1_53) = iProver_top
% 2.15/1.08      | v2_struct_0(X0_53) = iProver_top
% 2.15/1.08      | v2_struct_0(sK1) = iProver_top
% 2.15/1.08      | l1_pre_topc(X1_53) != iProver_top
% 2.15/1.08      | l1_pre_topc(sK1) != iProver_top
% 2.15/1.08      | v2_pre_topc(X1_53) != iProver_top
% 2.15/1.08      | v2_pre_topc(sK1) != iProver_top
% 2.15/1.08      | sP0_iProver_split != iProver_top ),
% 2.15/1.08      inference(equality_resolution,[status(thm)],[c_2001]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_35,negated_conjecture,
% 2.15/1.08      ( l1_pre_topc(sK0) ),
% 2.15/1.08      inference(cnf_transformation,[],[f69]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_40,plain,
% 2.15/1.08      ( l1_pre_topc(sK0) = iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_34,negated_conjecture,
% 2.15/1.08      ( ~ v2_struct_0(sK1) ),
% 2.15/1.08      inference(cnf_transformation,[],[f70]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_41,plain,
% 2.15/1.08      ( v2_struct_0(sK1) != iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_33,negated_conjecture,
% 2.15/1.08      ( v2_pre_topc(sK1) ),
% 2.15/1.08      inference(cnf_transformation,[],[f71]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_42,plain,
% 2.15/1.08      ( v2_pre_topc(sK1) = iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_32,negated_conjecture,
% 2.15/1.08      ( l1_pre_topc(sK1) ),
% 2.15/1.08      inference(cnf_transformation,[],[f72]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_43,plain,
% 2.15/1.08      ( l1_pre_topc(sK1) = iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_31,negated_conjecture,
% 2.15/1.08      ( ~ v2_struct_0(sK2) ),
% 2.15/1.08      inference(cnf_transformation,[],[f73]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_44,plain,
% 2.15/1.08      ( v2_struct_0(sK2) != iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_28,negated_conjecture,
% 2.15/1.08      ( m1_pre_topc(sK3,sK0) ),
% 2.15/1.08      inference(cnf_transformation,[],[f76]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_47,plain,
% 2.15/1.08      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_25,negated_conjecture,
% 2.15/1.08      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.15/1.08      inference(cnf_transformation,[],[f79]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_50,plain,
% 2.15/1.08      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_52,plain,
% 2.15/1.08      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1325,plain,
% 2.15/1.08      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.08      | v1_xboole_0(u1_struct_0(sK2))
% 2.15/1.08      | sP0_iProver_split ),
% 2.15/1.08      inference(splitting,
% 2.15/1.08                [splitting(split),new_symbols(definition,[])],
% 2.15/1.08                [c_1296]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1375,plain,
% 2.15/1.08      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.15/1.08      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 2.15/1.08      | sP0_iProver_split = iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_1325]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1319,plain,
% 2.15/1.08      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.15/1.08      | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53)))
% 2.15/1.08      | ~ l1_pre_topc(X1_53) ),
% 2.15/1.08      inference(subtyping,[status(esa)],[c_11]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2250,plain,
% 2.15/1.08      ( ~ m1_pre_topc(sK2,sK3)
% 2.15/1.08      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.15/1.08      | ~ l1_pre_topc(sK3) ),
% 2.15/1.08      inference(instantiation,[status(thm)],[c_1319]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2251,plain,
% 2.15/1.08      ( m1_pre_topc(sK2,sK3) != iProver_top
% 2.15/1.08      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.15/1.08      | l1_pre_topc(sK3) != iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_2250]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1320,plain,
% 2.15/1.08      ( ~ m1_pre_topc(X0_53,X1_53)
% 2.15/1.08      | ~ l1_pre_topc(X1_53)
% 2.15/1.08      | l1_pre_topc(X0_53) ),
% 2.15/1.08      inference(subtyping,[status(esa)],[c_6]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2335,plain,
% 2.15/1.08      ( ~ m1_pre_topc(sK3,X0_53)
% 2.15/1.08      | ~ l1_pre_topc(X0_53)
% 2.15/1.08      | l1_pre_topc(sK3) ),
% 2.15/1.08      inference(instantiation,[status(thm)],[c_1320]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2506,plain,
% 2.15/1.08      ( ~ m1_pre_topc(sK3,sK0) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK0) ),
% 2.15/1.08      inference(instantiation,[status(thm)],[c_2335]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2507,plain,
% 2.15/1.08      ( m1_pre_topc(sK3,sK0) != iProver_top
% 2.15/1.08      | l1_pre_topc(sK3) = iProver_top
% 2.15/1.08      | l1_pre_topc(sK0) != iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_2506]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_5,plain,
% 2.15/1.08      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 2.15/1.08      inference(cnf_transformation,[],[f54]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_7,plain,
% 2.15/1.08      ( v2_struct_0(X0)
% 2.15/1.08      | ~ l1_struct_0(X0)
% 2.15/1.08      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.15/1.08      inference(cnf_transformation,[],[f56]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_470,plain,
% 2.15/1.08      ( v2_struct_0(X0)
% 2.15/1.08      | ~ l1_pre_topc(X0)
% 2.15/1.08      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.15/1.08      inference(resolution,[status(thm)],[c_5,c_7]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1298,plain,
% 2.15/1.08      ( v2_struct_0(X0_53)
% 2.15/1.08      | ~ l1_pre_topc(X0_53)
% 2.15/1.08      | ~ v1_xboole_0(u1_struct_0(X0_53)) ),
% 2.15/1.08      inference(subtyping,[status(esa)],[c_470]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2579,plain,
% 2.15/1.08      ( v2_struct_0(sK2)
% 2.15/1.08      | ~ l1_pre_topc(sK2)
% 2.15/1.08      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.15/1.08      inference(instantiation,[status(thm)],[c_1298]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2580,plain,
% 2.15/1.08      ( v2_struct_0(sK2) = iProver_top
% 2.15/1.08      | l1_pre_topc(sK2) != iProver_top
% 2.15/1.08      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_2579]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1310,negated_conjecture,
% 2.15/1.08      ( m1_pre_topc(sK2,sK3) ),
% 2.15/1.08      inference(subtyping,[status(esa)],[c_23]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1986,plain,
% 2.15/1.08      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_1310]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1977,plain,
% 2.15/1.08      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.15/1.08      | l1_pre_topc(X1_53) != iProver_top
% 2.15/1.08      | l1_pre_topc(X0_53) = iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_1320]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2839,plain,
% 2.15/1.08      ( l1_pre_topc(sK3) != iProver_top
% 2.15/1.08      | l1_pre_topc(sK2) = iProver_top ),
% 2.15/1.08      inference(superposition,[status(thm)],[c_1986,c_1977]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_3560,plain,
% 2.15/1.08      ( l1_pre_topc(X1_53) != iProver_top
% 2.15/1.08      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 2.15/1.08      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 2.15/1.08      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.15/1.08      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.15/1.08      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.15/1.08      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
% 2.15/1.08      | r1_tmap_1(sK3,sK1,sK4,X0_54) = iProver_top
% 2.15/1.08      | r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_54) != iProver_top
% 2.15/1.08      | v2_struct_0(X1_53) = iProver_top
% 2.15/1.08      | v2_struct_0(X0_53) = iProver_top
% 2.15/1.08      | v2_pre_topc(X1_53) != iProver_top ),
% 2.15/1.08      inference(global_propositional_subsumption,
% 2.15/1.08                [status(thm)],
% 2.15/1.08                [c_2682,c_40,c_41,c_42,c_43,c_44,c_47,c_50,c_52,c_1375,
% 2.15/1.08                 c_2251,c_2507,c_2580,c_2839]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_3561,plain,
% 2.15/1.08      ( r1_tmap_1(X0_53,sK1,k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_54) != iProver_top
% 2.15/1.08      | r1_tmap_1(sK3,sK1,sK4,X0_54) = iProver_top
% 2.15/1.08      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
% 2.15/1.08      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.15/1.08      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.15/1.08      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 2.15/1.08      | m1_subset_1(X0_54,u1_struct_0(sK3)) != iProver_top
% 2.15/1.08      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 2.15/1.08      | v2_struct_0(X1_53) = iProver_top
% 2.15/1.08      | v2_struct_0(X0_53) = iProver_top
% 2.15/1.08      | l1_pre_topc(X1_53) != iProver_top
% 2.15/1.08      | v2_pre_topc(X1_53) != iProver_top ),
% 2.15/1.08      inference(renaming,[status(thm)],[c_3560]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_3578,plain,
% 2.15/1.08      ( r1_tmap_1(sK3,sK1,sK4,sK6) = iProver_top
% 2.15/1.08      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.15/1.08      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.15/1.08      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.15/1.08      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.15/1.08      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 2.15/1.08      | v2_struct_0(sK0) = iProver_top
% 2.15/1.08      | v2_struct_0(sK2) = iProver_top
% 2.15/1.08      | l1_pre_topc(sK0) != iProver_top
% 2.15/1.08      | v2_pre_topc(sK0) != iProver_top ),
% 2.15/1.08      inference(superposition,[status(thm)],[c_2073,c_3561]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_37,negated_conjecture,
% 2.15/1.08      ( ~ v2_struct_0(sK0) ),
% 2.15/1.08      inference(cnf_transformation,[],[f67]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_38,plain,
% 2.15/1.08      ( v2_struct_0(sK0) != iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_36,negated_conjecture,
% 2.15/1.08      ( v2_pre_topc(sK0) ),
% 2.15/1.08      inference(cnf_transformation,[],[f68]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_39,plain,
% 2.15/1.08      ( v2_pre_topc(sK0) = iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_46,plain,
% 2.15/1.08      ( v2_struct_0(sK3) != iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_21,negated_conjecture,
% 2.15/1.08      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 2.15/1.08      inference(cnf_transformation,[],[f83]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_54,plain,
% 2.15/1.08      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_22,negated_conjecture,
% 2.15/1.08      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 2.15/1.08      inference(cnf_transformation,[],[f82]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1311,negated_conjecture,
% 2.15/1.08      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 2.15/1.08      inference(subtyping,[status(esa)],[c_22]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1985,plain,
% 2.15/1.08      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_1311]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2028,plain,
% 2.15/1.08      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.15/1.08      inference(light_normalisation,[status(thm)],[c_1985,c_1313]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_18,negated_conjecture,
% 2.15/1.08      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
% 2.15/1.08      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 2.15/1.08      inference(cnf_transformation,[],[f86]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1315,negated_conjecture,
% 2.15/1.08      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
% 2.15/1.08      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 2.15/1.08      inference(subtyping,[status(esa)],[c_18]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1982,plain,
% 2.15/1.08      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top
% 2.15/1.08      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) != iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_1315]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2084,plain,
% 2.15/1.08      ( r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
% 2.15/1.08      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) != iProver_top ),
% 2.15/1.08      inference(light_normalisation,[status(thm)],[c_1982,c_1313]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1327,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2244,plain,
% 2.15/1.08      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 2.15/1.08      inference(instantiation,[status(thm)],[c_1327]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2361,plain,
% 2.15/1.08      ( u1_struct_0(X0_53) = u1_struct_0(X0_53) ),
% 2.15/1.08      inference(instantiation,[status(thm)],[c_1327]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2366,plain,
% 2.15/1.08      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 2.15/1.08      inference(instantiation,[status(thm)],[c_2361]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_17,plain,
% 2.15/1.08      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.15/1.08      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.15/1.08      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.15/1.08      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.15/1.08      | ~ v3_pre_topc(X6,X0)
% 2.15/1.08      | ~ m1_pre_topc(X0,X5)
% 2.15/1.08      | ~ m1_pre_topc(X4,X5)
% 2.15/1.08      | ~ m1_pre_topc(X4,X0)
% 2.15/1.08      | ~ r2_hidden(X3,X6)
% 2.15/1.08      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.15/1.08      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.15/1.08      | ~ v1_funct_1(X2)
% 2.15/1.08      | v2_struct_0(X5)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X4)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | ~ l1_pre_topc(X5)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X5)
% 2.15/1.08      | ~ v2_pre_topc(X1) ),
% 2.15/1.08      inference(cnf_transformation,[],[f92]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_15,plain,
% 2.15/1.08      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.15/1.08      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.15/1.08      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.15/1.08      | ~ m1_pre_topc(X4,X0)
% 2.15/1.08      | ~ m1_pre_topc(X4,X5)
% 2.15/1.08      | ~ m1_pre_topc(X0,X5)
% 2.15/1.08      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.15/1.08      | ~ v1_funct_1(X2)
% 2.15/1.08      | v2_struct_0(X5)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(X4)
% 2.15/1.08      | ~ l1_pre_topc(X5)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X5)
% 2.15/1.08      | ~ v2_pre_topc(X1) ),
% 2.15/1.08      inference(cnf_transformation,[],[f90]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_195,plain,
% 2.15/1.08      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.15/1.08      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.15/1.08      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.15/1.08      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.15/1.08      | ~ m1_pre_topc(X0,X5)
% 2.15/1.08      | ~ m1_pre_topc(X4,X5)
% 2.15/1.08      | ~ m1_pre_topc(X4,X0)
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.15/1.08      | ~ v1_funct_1(X2)
% 2.15/1.08      | v2_struct_0(X5)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X4)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | ~ l1_pre_topc(X5)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X5)
% 2.15/1.08      | ~ v2_pre_topc(X1) ),
% 2.15/1.08      inference(global_propositional_subsumption,
% 2.15/1.08                [status(thm)],
% 2.15/1.08                [c_17,c_15]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_196,plain,
% 2.15/1.08      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.15/1.08      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.15/1.08      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.15/1.08      | ~ m1_pre_topc(X4,X0)
% 2.15/1.08      | ~ m1_pre_topc(X4,X5)
% 2.15/1.08      | ~ m1_pre_topc(X0,X5)
% 2.15/1.08      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.15/1.08      | ~ v1_funct_1(X2)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(X5)
% 2.15/1.08      | v2_struct_0(X4)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X5)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X5) ),
% 2.15/1.08      inference(renaming,[status(thm)],[c_195]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_757,plain,
% 2.15/1.08      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.15/1.08      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.15/1.08      | ~ m1_pre_topc(X4,X0)
% 2.15/1.08      | ~ m1_pre_topc(X4,X5)
% 2.15/1.08      | ~ m1_pre_topc(X0,X5)
% 2.15/1.08      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.15/1.08      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.15/1.08      | ~ v1_funct_1(X2)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(X5)
% 2.15/1.08      | v2_struct_0(X4)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X5)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X5)
% 2.15/1.08      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.15/1.08      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.15/1.08      | sK4 != X2 ),
% 2.15/1.08      inference(resolution_lifted,[status(thm)],[c_196,c_26]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_758,plain,
% 2.15/1.08      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.15/1.08      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.15/1.08      | ~ m1_pre_topc(X0,X3)
% 2.15/1.08      | ~ m1_pre_topc(X0,X2)
% 2.15/1.08      | ~ m1_pre_topc(X3,X2)
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.15/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.15/1.08      | ~ v1_funct_1(sK4)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X3)
% 2.15/1.08      | v2_struct_0(X2)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X2)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X2)
% 2.15/1.08      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.15/1.08      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.15/1.08      inference(unflattening,[status(thm)],[c_757]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_762,plain,
% 2.15/1.08      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.15/1.08      | ~ m1_pre_topc(X3,X2)
% 2.15/1.08      | ~ m1_pre_topc(X0,X2)
% 2.15/1.08      | ~ m1_pre_topc(X0,X3)
% 2.15/1.08      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.15/1.08      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X3)
% 2.15/1.08      | v2_struct_0(X2)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X2)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X2)
% 2.15/1.08      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.15/1.08      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.15/1.08      inference(global_propositional_subsumption,
% 2.15/1.08                [status(thm)],
% 2.15/1.08                [c_758,c_27]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_763,plain,
% 2.15/1.08      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.15/1.08      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.15/1.08      | ~ m1_pre_topc(X3,X2)
% 2.15/1.08      | ~ m1_pre_topc(X0,X2)
% 2.15/1.08      | ~ m1_pre_topc(X0,X3)
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.15/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(X2)
% 2.15/1.08      | v2_struct_0(X3)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X2)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X2)
% 2.15/1.08      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.15/1.08      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.15/1.08      inference(renaming,[status(thm)],[c_762]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_804,plain,
% 2.15/1.08      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.15/1.08      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.15/1.08      | ~ m1_pre_topc(X3,X2)
% 2.15/1.08      | ~ m1_pre_topc(X0,X3)
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.15/1.08      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.15/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.15/1.08      | v2_struct_0(X1)
% 2.15/1.08      | v2_struct_0(X0)
% 2.15/1.08      | v2_struct_0(X2)
% 2.15/1.08      | v2_struct_0(X3)
% 2.15/1.08      | ~ l1_pre_topc(X1)
% 2.15/1.08      | ~ l1_pre_topc(X2)
% 2.15/1.08      | ~ v2_pre_topc(X1)
% 2.15/1.08      | ~ v2_pre_topc(X2)
% 2.15/1.08      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.15/1.08      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.15/1.08      inference(forward_subsumption_resolution,
% 2.15/1.08                [status(thm)],
% 2.15/1.08                [c_763,c_14]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_1297,plain,
% 2.15/1.08      ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,X3_53,X0_53,sK4),X0_54)
% 2.15/1.08      | ~ r1_tmap_1(X3_53,X1_53,sK4,X0_54)
% 2.15/1.08      | ~ m1_pre_topc(X3_53,X2_53)
% 2.15/1.08      | ~ m1_pre_topc(X0_53,X3_53)
% 2.15/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.15/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(X3_53))
% 2.15/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53))))
% 2.15/1.08      | v2_struct_0(X1_53)
% 2.15/1.08      | v2_struct_0(X0_53)
% 2.15/1.08      | v2_struct_0(X2_53)
% 2.15/1.08      | v2_struct_0(X3_53)
% 2.15/1.08      | ~ l1_pre_topc(X1_53)
% 2.15/1.08      | ~ l1_pre_topc(X2_53)
% 2.15/1.08      | ~ v2_pre_topc(X1_53)
% 2.15/1.08      | ~ v2_pre_topc(X2_53)
% 2.15/1.08      | u1_struct_0(X3_53) != u1_struct_0(sK3)
% 2.15/1.08      | u1_struct_0(X1_53) != u1_struct_0(sK1) ),
% 2.15/1.08      inference(subtyping,[status(esa)],[c_804]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2245,plain,
% 2.15/1.08      ( r1_tmap_1(X0_53,X1_53,k3_tmap_1(X2_53,X1_53,sK3,X0_53,sK4),X0_54)
% 2.15/1.08      | ~ r1_tmap_1(sK3,X1_53,sK4,X0_54)
% 2.15/1.08      | ~ m1_pre_topc(X0_53,sK3)
% 2.15/1.08      | ~ m1_pre_topc(sK3,X2_53)
% 2.15/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(X0_53))
% 2.15/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_53))))
% 2.15/1.08      | v2_struct_0(X1_53)
% 2.15/1.08      | v2_struct_0(X0_53)
% 2.15/1.08      | v2_struct_0(X2_53)
% 2.15/1.08      | v2_struct_0(sK3)
% 2.15/1.08      | ~ l1_pre_topc(X1_53)
% 2.15/1.08      | ~ l1_pre_topc(X2_53)
% 2.15/1.08      | ~ v2_pre_topc(X1_53)
% 2.15/1.08      | ~ v2_pre_topc(X2_53)
% 2.15/1.08      | u1_struct_0(X1_53) != u1_struct_0(sK1)
% 2.15/1.08      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.15/1.08      inference(instantiation,[status(thm)],[c_1297]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2344,plain,
% 2.15/1.08      ( ~ r1_tmap_1(sK3,X0_53,sK4,X0_54)
% 2.15/1.08      | r1_tmap_1(sK2,X0_53,k3_tmap_1(X1_53,X0_53,sK3,sK2,sK4),X0_54)
% 2.15/1.08      | ~ m1_pre_topc(sK3,X1_53)
% 2.15/1.08      | ~ m1_pre_topc(sK2,sK3)
% 2.15/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 2.15/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 2.15/1.08      | v2_struct_0(X1_53)
% 2.15/1.08      | v2_struct_0(X0_53)
% 2.15/1.08      | v2_struct_0(sK3)
% 2.15/1.08      | v2_struct_0(sK2)
% 2.15/1.08      | ~ l1_pre_topc(X1_53)
% 2.15/1.08      | ~ l1_pre_topc(X0_53)
% 2.15/1.08      | ~ v2_pre_topc(X1_53)
% 2.15/1.08      | ~ v2_pre_topc(X0_53)
% 2.15/1.08      | u1_struct_0(X0_53) != u1_struct_0(sK1)
% 2.15/1.08      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.15/1.08      inference(instantiation,[status(thm)],[c_2245]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_2696,plain,
% 2.15/1.08      ( ~ r1_tmap_1(sK3,X0_53,sK4,X0_54)
% 2.15/1.08      | r1_tmap_1(sK2,X0_53,k3_tmap_1(sK0,X0_53,sK3,sK2,sK4),X0_54)
% 2.15/1.08      | ~ m1_pre_topc(sK3,sK0)
% 2.15/1.08      | ~ m1_pre_topc(sK2,sK3)
% 2.15/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 2.15/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 2.15/1.08      | v2_struct_0(X0_53)
% 2.15/1.08      | v2_struct_0(sK3)
% 2.15/1.08      | v2_struct_0(sK0)
% 2.15/1.08      | v2_struct_0(sK2)
% 2.15/1.08      | ~ l1_pre_topc(X0_53)
% 2.15/1.08      | ~ l1_pre_topc(sK0)
% 2.15/1.08      | ~ v2_pre_topc(X0_53)
% 2.15/1.08      | ~ v2_pre_topc(sK0)
% 2.15/1.08      | u1_struct_0(X0_53) != u1_struct_0(sK1)
% 2.15/1.08      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.15/1.08      inference(instantiation,[status(thm)],[c_2344]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_3421,plain,
% 2.15/1.08      ( ~ r1_tmap_1(sK3,X0_53,sK4,sK6)
% 2.15/1.08      | r1_tmap_1(sK2,X0_53,k3_tmap_1(sK0,X0_53,sK3,sK2,sK4),sK6)
% 2.15/1.08      | ~ m1_pre_topc(sK3,sK0)
% 2.15/1.08      | ~ m1_pre_topc(sK2,sK3)
% 2.15/1.08      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.15/1.08      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.15/1.08      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53))))
% 2.15/1.08      | v2_struct_0(X0_53)
% 2.15/1.08      | v2_struct_0(sK3)
% 2.15/1.08      | v2_struct_0(sK0)
% 2.15/1.08      | v2_struct_0(sK2)
% 2.15/1.08      | ~ l1_pre_topc(X0_53)
% 2.15/1.08      | ~ l1_pre_topc(sK0)
% 2.15/1.08      | ~ v2_pre_topc(X0_53)
% 2.15/1.08      | ~ v2_pre_topc(sK0)
% 2.15/1.08      | u1_struct_0(X0_53) != u1_struct_0(sK1)
% 2.15/1.08      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.15/1.08      inference(instantiation,[status(thm)],[c_2696]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_3427,plain,
% 2.15/1.08      ( u1_struct_0(X0_53) != u1_struct_0(sK1)
% 2.15/1.08      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.15/1.08      | r1_tmap_1(sK3,X0_53,sK4,sK6) != iProver_top
% 2.15/1.08      | r1_tmap_1(sK2,X0_53,k3_tmap_1(sK0,X0_53,sK3,sK2,sK4),sK6) = iProver_top
% 2.15/1.08      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.15/1.08      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.15/1.08      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.15/1.08      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 2.15/1.08      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_53)))) != iProver_top
% 2.15/1.08      | v2_struct_0(X0_53) = iProver_top
% 2.15/1.08      | v2_struct_0(sK3) = iProver_top
% 2.15/1.08      | v2_struct_0(sK0) = iProver_top
% 2.15/1.08      | v2_struct_0(sK2) = iProver_top
% 2.15/1.08      | l1_pre_topc(X0_53) != iProver_top
% 2.15/1.08      | l1_pre_topc(sK0) != iProver_top
% 2.15/1.08      | v2_pre_topc(X0_53) != iProver_top
% 2.15/1.08      | v2_pre_topc(sK0) != iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_3421]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_3429,plain,
% 2.15/1.08      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.15/1.08      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.15/1.08      | r1_tmap_1(sK3,sK1,sK4,sK6) != iProver_top
% 2.15/1.08      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top
% 2.15/1.08      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.15/1.08      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.15/1.08      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.15/1.08      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 2.15/1.08      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.15/1.08      | v2_struct_0(sK3) = iProver_top
% 2.15/1.08      | v2_struct_0(sK0) = iProver_top
% 2.15/1.08      | v2_struct_0(sK1) = iProver_top
% 2.15/1.08      | v2_struct_0(sK2) = iProver_top
% 2.15/1.08      | l1_pre_topc(sK0) != iProver_top
% 2.15/1.08      | l1_pre_topc(sK1) != iProver_top
% 2.15/1.08      | v2_pre_topc(sK0) != iProver_top
% 2.15/1.08      | v2_pre_topc(sK1) != iProver_top ),
% 2.15/1.08      inference(instantiation,[status(thm)],[c_3427]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_3716,plain,
% 2.15/1.08      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top ),
% 2.15/1.08      inference(global_propositional_subsumption,
% 2.15/1.08                [status(thm)],
% 2.15/1.08                [c_3578,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_46,c_47,
% 2.15/1.08                 c_50,c_52,c_54,c_2028,c_2084,c_2244,c_2366,c_3429]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_3721,plain,
% 2.15/1.08      ( m1_pre_topc(sK2,sK2) != iProver_top
% 2.15/1.08      | l1_pre_topc(sK2) != iProver_top ),
% 2.15/1.08      inference(superposition,[status(thm)],[c_1980,c_3716]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_3392,plain,
% 2.15/1.08      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2))
% 2.15/1.08      | ~ m1_pre_topc(sK2,sK2)
% 2.15/1.08      | ~ l1_pre_topc(sK2) ),
% 2.15/1.08      inference(instantiation,[status(thm)],[c_1317]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_3393,plain,
% 2.15/1.08      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
% 2.15/1.08      | m1_pre_topc(sK2,sK2) != iProver_top
% 2.15/1.08      | l1_pre_topc(sK2) != iProver_top ),
% 2.15/1.08      inference(predicate_to_equality,[status(thm)],[c_3392]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_3724,plain,
% 2.15/1.08      ( m1_pre_topc(sK2,sK2) != iProver_top ),
% 2.15/1.08      inference(global_propositional_subsumption,
% 2.15/1.08                [status(thm)],
% 2.15/1.08                [c_3721,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_46,c_47,
% 2.15/1.08                 c_50,c_52,c_54,c_2028,c_2084,c_2244,c_2366,c_2507,
% 2.15/1.08                 c_2839,c_3393,c_3429,c_3578]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(c_3729,plain,
% 2.15/1.08      ( l1_pre_topc(sK2) != iProver_top ),
% 2.15/1.08      inference(superposition,[status(thm)],[c_1979,c_3724]) ).
% 2.15/1.08  
% 2.15/1.08  cnf(contradiction,plain,
% 2.15/1.08      ( $false ),
% 2.15/1.08      inference(minisat,[status(thm)],[c_3729,c_2839,c_2507,c_47,c_40]) ).
% 2.15/1.08  
% 2.15/1.08  
% 2.15/1.08  % SZS output end CNFRefutation for theBenchmark.p
% 2.15/1.08  
% 2.15/1.08  ------                               Statistics
% 2.15/1.08  
% 2.15/1.08  ------ General
% 2.15/1.08  
% 2.15/1.08  abstr_ref_over_cycles:                  0
% 2.15/1.08  abstr_ref_under_cycles:                 0
% 2.15/1.08  gc_basic_clause_elim:                   0
% 2.15/1.08  forced_gc_time:                         0
% 2.15/1.08  parsing_time:                           0.013
% 2.15/1.08  unif_index_cands_time:                  0.
% 2.15/1.08  unif_index_add_time:                    0.
% 2.15/1.08  orderings_time:                         0.
% 2.15/1.08  out_proof_time:                         0.066
% 2.15/1.08  total_time:                             0.244
% 2.15/1.08  num_of_symbols:                         59
% 2.15/1.08  num_of_terms:                           2495
% 2.15/1.08  
% 2.15/1.08  ------ Preprocessing
% 2.15/1.08  
% 2.15/1.08  num_of_splits:                          1
% 2.15/1.08  num_of_split_atoms:                     1
% 2.15/1.08  num_of_reused_defs:                     0
% 2.15/1.08  num_eq_ax_congr_red:                    16
% 2.15/1.08  num_of_sem_filtered_clauses:            1
% 2.15/1.08  num_of_subtypes:                        2
% 2.15/1.08  monotx_restored_types:                  0
% 2.15/1.08  sat_num_of_epr_types:                   0
% 2.15/1.08  sat_num_of_non_cyclic_types:            0
% 2.15/1.08  sat_guarded_non_collapsed_types:        0
% 2.15/1.08  num_pure_diseq_elim:                    0
% 2.15/1.08  simp_replaced_by:                       0
% 2.15/1.08  res_preprocessed:                       142
% 2.15/1.08  prep_upred:                             0
% 2.15/1.08  prep_unflattend:                        9
% 2.15/1.08  smt_new_axioms:                         0
% 2.15/1.08  pred_elim_cands:                        8
% 2.15/1.08  pred_elim:                              6
% 2.15/1.08  pred_elim_cl:                           9
% 2.15/1.08  pred_elim_cycles:                       10
% 2.15/1.08  merged_defs:                            8
% 2.15/1.08  merged_defs_ncl:                        0
% 2.15/1.08  bin_hyper_res:                          8
% 2.15/1.08  prep_cycles:                            4
% 2.15/1.08  pred_elim_time:                         0.03
% 2.15/1.08  splitting_time:                         0.
% 2.15/1.08  sem_filter_time:                        0.
% 2.15/1.08  monotx_time:                            0.
% 2.15/1.08  subtype_inf_time:                       0.
% 2.15/1.08  
% 2.15/1.08  ------ Problem properties
% 2.15/1.08  
% 2.15/1.08  clauses:                                29
% 2.15/1.08  conjectures:                            17
% 2.15/1.08  epr:                                    18
% 2.15/1.08  horn:                                   25
% 2.15/1.08  ground:                                 18
% 2.15/1.08  unary:                                  15
% 2.15/1.08  binary:                                 3
% 2.15/1.08  lits:                                   86
% 2.15/1.08  lits_eq:                                4
% 2.15/1.08  fd_pure:                                0
% 2.15/1.08  fd_pseudo:                              0
% 2.15/1.08  fd_cond:                                0
% 2.15/1.08  fd_pseudo_cond:                         0
% 2.15/1.08  ac_symbols:                             0
% 2.15/1.08  
% 2.15/1.08  ------ Propositional Solver
% 2.15/1.08  
% 2.15/1.08  prop_solver_calls:                      29
% 2.15/1.08  prop_fast_solver_calls:                 1357
% 2.15/1.08  smt_solver_calls:                       0
% 2.15/1.08  smt_fast_solver_calls:                  0
% 2.15/1.08  prop_num_of_clauses:                    771
% 2.15/1.08  prop_preprocess_simplified:             3954
% 2.15/1.08  prop_fo_subsumed:                       44
% 2.15/1.08  prop_solver_time:                       0.
% 2.15/1.08  smt_solver_time:                        0.
% 2.15/1.08  smt_fast_solver_time:                   0.
% 2.15/1.08  prop_fast_solver_time:                  0.
% 2.15/1.08  prop_unsat_core_time:                   0.
% 2.15/1.08  
% 2.15/1.08  ------ QBF
% 2.15/1.08  
% 2.15/1.08  qbf_q_res:                              0
% 2.15/1.08  qbf_num_tautologies:                    0
% 2.15/1.08  qbf_prep_cycles:                        0
% 2.15/1.08  
% 2.15/1.08  ------ BMC1
% 2.15/1.08  
% 2.15/1.08  bmc1_current_bound:                     -1
% 2.15/1.08  bmc1_last_solved_bound:                 -1
% 2.15/1.08  bmc1_unsat_core_size:                   -1
% 2.15/1.08  bmc1_unsat_core_parents_size:           -1
% 2.15/1.08  bmc1_merge_next_fun:                    0
% 2.15/1.08  bmc1_unsat_core_clauses_time:           0.
% 2.15/1.08  
% 2.15/1.08  ------ Instantiation
% 2.15/1.08  
% 2.15/1.08  inst_num_of_clauses:                    241
% 2.15/1.08  inst_num_in_passive:                    14
% 2.15/1.08  inst_num_in_active:                     189
% 2.15/1.08  inst_num_in_unprocessed:                38
% 2.15/1.08  inst_num_of_loops:                      210
% 2.15/1.08  inst_num_of_learning_restarts:          0
% 2.15/1.08  inst_num_moves_active_passive:          15
% 2.15/1.08  inst_lit_activity:                      0
% 2.15/1.08  inst_lit_activity_moves:                0
% 2.15/1.08  inst_num_tautologies:                   0
% 2.15/1.08  inst_num_prop_implied:                  0
% 2.15/1.08  inst_num_existing_simplified:           0
% 2.15/1.08  inst_num_eq_res_simplified:             0
% 2.15/1.08  inst_num_child_elim:                    0
% 2.15/1.08  inst_num_of_dismatching_blockings:      50
% 2.15/1.08  inst_num_of_non_proper_insts:           293
% 2.15/1.08  inst_num_of_duplicates:                 0
% 2.15/1.08  inst_inst_num_from_inst_to_res:         0
% 2.15/1.08  inst_dismatching_checking_time:         0.
% 2.15/1.08  
% 2.15/1.08  ------ Resolution
% 2.15/1.08  
% 2.15/1.08  res_num_of_clauses:                     0
% 2.15/1.08  res_num_in_passive:                     0
% 2.15/1.08  res_num_in_active:                      0
% 2.15/1.08  res_num_of_loops:                       146
% 2.15/1.08  res_forward_subset_subsumed:            48
% 2.15/1.08  res_backward_subset_subsumed:           4
% 2.15/1.08  res_forward_subsumed:                   0
% 2.15/1.08  res_backward_subsumed:                  0
% 2.15/1.08  res_forward_subsumption_resolution:     4
% 2.15/1.08  res_backward_subsumption_resolution:    0
% 2.15/1.08  res_clause_to_clause_subsumption:       236
% 2.15/1.08  res_orphan_elimination:                 0
% 2.15/1.08  res_tautology_del:                      140
% 2.15/1.08  res_num_eq_res_simplified:              0
% 2.15/1.08  res_num_sel_changes:                    0
% 2.15/1.08  res_moves_from_active_to_pass:          0
% 2.15/1.08  
% 2.15/1.08  ------ Superposition
% 2.15/1.08  
% 2.15/1.08  sup_time_total:                         0.
% 2.15/1.08  sup_time_generating:                    0.
% 2.15/1.08  sup_time_sim_full:                      0.
% 2.15/1.08  sup_time_sim_immed:                     0.
% 2.15/1.08  
% 2.15/1.08  sup_num_of_clauses:                     47
% 2.15/1.08  sup_num_in_active:                      42
% 2.15/1.08  sup_num_in_passive:                     5
% 2.15/1.08  sup_num_of_loops:                       41
% 2.15/1.08  sup_fw_superposition:                   24
% 2.15/1.08  sup_bw_superposition:                   2
% 2.15/1.08  sup_immediate_simplified:               3
% 2.15/1.08  sup_given_eliminated:                   0
% 2.15/1.08  comparisons_done:                       0
% 2.15/1.08  comparisons_avoided:                    0
% 2.15/1.08  
% 2.15/1.08  ------ Simplifications
% 2.15/1.08  
% 2.15/1.08  
% 2.15/1.08  sim_fw_subset_subsumed:                 3
% 2.15/1.08  sim_bw_subset_subsumed:                 0
% 2.15/1.08  sim_fw_subsumed:                        0
% 2.15/1.08  sim_bw_subsumed:                        0
% 2.15/1.08  sim_fw_subsumption_res:                 0
% 2.15/1.08  sim_bw_subsumption_res:                 0
% 2.15/1.08  sim_tautology_del:                      5
% 2.15/1.08  sim_eq_tautology_del:                   0
% 2.15/1.08  sim_eq_res_simp:                        0
% 2.15/1.08  sim_fw_demodulated:                     0
% 2.15/1.08  sim_bw_demodulated:                     0
% 2.15/1.08  sim_light_normalised:                   3
% 2.15/1.08  sim_joinable_taut:                      0
% 2.15/1.08  sim_joinable_simp:                      0
% 2.15/1.08  sim_ac_normalised:                      0
% 2.15/1.08  sim_smt_subsumption:                    0
% 2.15/1.08  
%------------------------------------------------------------------------------
