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
% DateTime   : Thu Dec  3 12:23:22 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  201 (1410 expanded)
%              Number of clauses        :  129 ( 277 expanded)
%              Number of leaves         :   18 ( 587 expanded)
%              Depth                    :   27
%              Number of atoms          : 1524 (27102 expanded)
%              Number of equality atoms :  347 (2047 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal clause size      :   46 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
            | ~ r1_tmap_1(X3,X0,X4,X5) )
          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
            | r1_tmap_1(X3,X0,X4,X5) )
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6)
          | ~ r1_tmap_1(X3,X0,X4,X5) )
        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6)
          | r1_tmap_1(X3,X0,X4,X5) )
        & sK6 = X5
        & m1_subset_1(sK6,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
              | ~ r1_tmap_1(X3,X0,X4,sK5) )
            & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
              | r1_tmap_1(X3,X0,X4,sK5) )
            & sK5 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6)
                  | ~ r1_tmap_1(X3,X0,sK4,X5) )
                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6)
                  | r1_tmap_1(X3,X0,sK4,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & m1_pre_topc(X2,X1)
        & v1_tsep_1(X2,X1)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6)
                      | ~ r1_tmap_1(sK3,X0,X4,X5) )
                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6)
                      | r1_tmap_1(sK3,X0,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & m1_pre_topc(X2,sK3)
            & m1_pre_topc(X2,X1)
            & v1_tsep_1(X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
                        ( ( ~ r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6)
                          | ~ r1_tmap_1(X3,X0,X4,X5) )
                        & ( r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6)
                          | r1_tmap_1(X3,X0,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK2,X3)
                & m1_pre_topc(sK2,X1)
                & v1_tsep_1(sK2,X1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X1)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
                            ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,X0,X4,X5) )
                            & ( r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6)
                              | r1_tmap_1(X3,X0,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X2,sK1)
                    & v1_tsep_1(X2,sK1)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
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
                              ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,sK0,X4,X5) )
                              & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,sK0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
      | ~ r1_tmap_1(sK3,sK0,sK4,sK5) )
    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
      | r1_tmap_1(sK3,sK0,sK4,sK5) )
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK2,sK1)
    & v1_tsep_1(sK2,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f32,f39,f38,f37,f36,f35,f34,f33])).

fof(f61,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f40])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
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
    inference(equality_resolution,[],[f49])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
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
    inference(equality_resolution,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_943,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1573,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_943])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_947,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1569,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_583,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X4) != u1_struct_0(sK0)
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_584,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_588,plain,
    ( v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_21])).

cnf(c_589,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_588])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_620,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_589,c_10])).

cnf(c_930,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X1_51,X2_51)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_51),u1_struct_0(X3_51))))
    | v2_struct_0(X2_51)
    | v2_struct_0(X3_51)
    | ~ l1_pre_topc(X2_51)
    | ~ l1_pre_topc(X3_51)
    | ~ v2_pre_topc(X2_51)
    | ~ v2_pre_topc(X3_51)
    | k2_partfun1(u1_struct_0(X1_51),u1_struct_0(X3_51),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X2_51,X3_51,X1_51,X0_51,sK4)
    | u1_struct_0(X1_51) != u1_struct_0(sK3)
    | u1_struct_0(X3_51) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_620])).

cnf(c_1586,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK4,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,sK4)
    | u1_struct_0(X0_51) != u1_struct_0(sK3)
    | u1_struct_0(X1_51) != u1_struct_0(sK0)
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X3_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X3_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_930])).

cnf(c_3079,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK0),sK4,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK0,X0_51,X1_51,sK4)
    | u1_struct_0(X0_51) != u1_struct_0(sK3)
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1586])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_32,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_33,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_34,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3270,plain,
    ( v2_pre_topc(X2_51) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | u1_struct_0(X0_51) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK0),sK4,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK0,X0_51,X1_51,sK4)
    | l1_pre_topc(X2_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3079,c_32,c_33,c_34])).

cnf(c_3271,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK0),sK4,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK0,X0_51,X1_51,sK4)
    | u1_struct_0(X0_51) != u1_struct_0(sK3)
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_3270])).

cnf(c_3282,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK0,sK3,X0_51,sK4)
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3271])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3309,plain,
    ( m1_pre_topc(sK3,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK0,sK3,X0_51,sK4)
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3282,c_44])).

cnf(c_3310,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK0,sK3,X0_51,sK4)
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_3309])).

cnf(c_3321,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0_51,sK0,sK3,sK2,sK4)
    | m1_pre_topc(sK3,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_3310])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_634,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_635,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_639,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_635,c_21])).

cnf(c_640,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X2) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_639])).

cnf(c_929,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_51),u1_struct_0(X2_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | k2_partfun1(u1_struct_0(X1_51),u1_struct_0(X2_51),sK4,u1_struct_0(X0_51)) = k2_tmap_1(X1_51,X2_51,sK4,X0_51)
    | u1_struct_0(X1_51) != u1_struct_0(sK3)
    | u1_struct_0(X2_51) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_640])).

cnf(c_1587,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK4,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,sK4,X2_51)
    | u1_struct_0(X0_51) != u1_struct_0(sK3)
    | u1_struct_0(X1_51) != u1_struct_0(sK0)
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_929])).

cnf(c_2656,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK0),sK4,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK0,sK4,X1_51)
    | u1_struct_0(X0_51) != u1_struct_0(sK3)
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1587])).

cnf(c_3051,plain,
    ( v2_pre_topc(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | u1_struct_0(X0_51) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK0),sK4,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK0,sK4,X1_51)
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2656,c_32,c_33,c_34])).

cnf(c_3052,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK0),sK4,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK0,sK4,X1_51)
    | u1_struct_0(X0_51) != u1_struct_0(sK3)
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_3051])).

cnf(c_3062,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK0,sK4,X0_51)
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3052])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_40,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_41,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_956,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | v2_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1561,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_956])).

cnf(c_2049,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1573,c_1561])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_955,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2052,plain,
    ( ~ m1_pre_topc(sK3,X0_51)
    | ~ l1_pre_topc(X0_51)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_955])).

cnf(c_2140,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2052])).

cnf(c_2141,plain,
    ( m1_pre_topc(sK3,sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2140])).

cnf(c_3219,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK0,sK4,X0_51)
    | m1_pre_topc(X0_51,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3062,c_36,c_37,c_40,c_41,c_44,c_2049,c_2141])).

cnf(c_3227,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK0,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_1569,c_3219])).

cnf(c_3322,plain,
    ( k3_tmap_1(X0_51,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2)
    | m1_pre_topc(sK3,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3321,c_3227])).

cnf(c_3332,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2)
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1573,c_3322])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3370,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3332,c_35,c_36,c_37])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_952,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1565,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_952])).

cnf(c_13,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_950,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1638,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1565,c_950])).

cnf(c_3374,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3370,c_1638])).

cnf(c_12,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_951,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1566,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_951])).

cnf(c_1627,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1566,c_950])).

cnf(c_3373,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3370,c_1627])).

cnf(c_9,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_463,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_464,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_468,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ v1_tsep_1(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_464,c_21])).

cnf(c_469,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_468])).

cnf(c_932,plain,
    ( r1_tmap_1(X0_51,X1_51,k2_tmap_1(X2_51,X1_51,sK4,X0_51),X0_52)
    | ~ r1_tmap_1(X2_51,X1_51,sK4,X0_52)
    | ~ v1_tsep_1(X0_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X2_51))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | u1_struct_0(X2_51) != u1_struct_0(sK3)
    | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_469])).

cnf(c_2110,plain,
    ( r1_tmap_1(X0_51,X1_51,k2_tmap_1(sK3,X1_51,sK4,X0_51),X0_52)
    | ~ r1_tmap_1(sK3,X1_51,sK4,X0_52)
    | ~ v1_tsep_1(X0_51,sK3)
    | ~ m1_pre_topc(X0_51,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X1_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_932])).

cnf(c_2273,plain,
    ( ~ r1_tmap_1(sK3,X0_51,sK4,X0_52)
    | r1_tmap_1(sK2,X0_51,k2_tmap_1(sK3,X0_51,sK4,sK2),X0_52)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2110])).

cnf(c_3110,plain,
    ( ~ r1_tmap_1(sK3,X0_51,sK4,sK6)
    | r1_tmap_1(sK2,X0_51,k2_tmap_1(sK3,X0_51,sK4,sK2),sK6)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2273])).

cnf(c_3111,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(sK3,X0_51,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,X0_51,k2_tmap_1(sK3,X0_51,sK4,sK2),sK6) = iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3110])).

cnf(c_3113,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) = iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3111])).

cnf(c_8,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_523,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_524,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_528,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ v1_tsep_1(X0,X2)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_21])).

cnf(c_529,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_528])).

cnf(c_931,plain,
    ( ~ r1_tmap_1(X0_51,X1_51,k2_tmap_1(X2_51,X1_51,sK4,X0_51),X0_52)
    | r1_tmap_1(X2_51,X1_51,sK4,X0_52)
    | ~ v1_tsep_1(X0_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X2_51))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | u1_struct_0(X2_51) != u1_struct_0(sK3)
    | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_529])).

cnf(c_2111,plain,
    ( ~ r1_tmap_1(X0_51,X1_51,k2_tmap_1(sK3,X1_51,sK4,X0_51),X0_52)
    | r1_tmap_1(sK3,X1_51,sK4,X0_52)
    | ~ v1_tsep_1(X0_51,sK3)
    | ~ m1_pre_topc(X0_51,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X1_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_931])).

cnf(c_2278,plain,
    ( r1_tmap_1(sK3,X0_51,sK4,X0_52)
    | ~ r1_tmap_1(sK2,X0_51,k2_tmap_1(sK3,X0_51,sK4,sK2),X0_52)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2111])).

cnf(c_2992,plain,
    ( r1_tmap_1(sK3,X0_51,sK4,sK6)
    | ~ r1_tmap_1(sK2,X0_51,k2_tmap_1(sK3,X0_51,sK4,sK2),sK6)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
    | v2_struct_0(X0_51)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2278])).

cnf(c_2993,plain,
    ( u1_struct_0(X0_51) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(sK3,X0_51,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,X0_51,k2_tmap_1(sK3,X0_51,sK4,sK2),sK6) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2992])).

cnf(c_2995,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2993])).

cnf(c_958,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_2618,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_381,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != X4
    | u1_struct_0(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_382,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_934,plain,
    ( ~ v1_tsep_1(X0_51,X1_51)
    | v1_tsep_1(X0_51,X2_51)
    | ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | ~ m1_subset_1(u1_struct_0(X0_51),k1_zfmisc_1(u1_struct_0(X2_51)))
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_382])).

cnf(c_1938,plain,
    ( v1_tsep_1(sK2,X0_51)
    | ~ v1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(X0_51,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0_51)))
    | v2_struct_0(X0_51)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_2060,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1938])).

cnf(c_2061,plain,
    ( v1_tsep_1(sK2,sK3) = iProver_top
    | v1_tsep_1(sK2,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2060])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_954,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | m1_subset_1(u1_struct_0(X0_51),k1_zfmisc_1(u1_struct_0(X1_51)))
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1900,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_1901,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1900])).

cnf(c_1870,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_948,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1568,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_1616,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1568,c_950])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_49,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_47,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_45,plain,
    ( v1_tsep_1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_39,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_38,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3374,c_3373,c_3113,c_2995,c_2618,c_2141,c_2061,c_2049,c_1901,c_1870,c_1616,c_49,c_47,c_45,c_44,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.23/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/0.98  
% 2.23/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.23/0.98  
% 2.23/0.98  ------  iProver source info
% 2.23/0.98  
% 2.23/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.23/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.23/0.98  git: non_committed_changes: false
% 2.23/0.98  git: last_make_outside_of_git: false
% 2.23/0.98  
% 2.23/0.98  ------ 
% 2.23/0.98  
% 2.23/0.98  ------ Input Options
% 2.23/0.98  
% 2.23/0.98  --out_options                           all
% 2.23/0.98  --tptp_safe_out                         true
% 2.23/0.98  --problem_path                          ""
% 2.23/0.98  --include_path                          ""
% 2.23/0.98  --clausifier                            res/vclausify_rel
% 2.23/0.98  --clausifier_options                    --mode clausify
% 2.23/0.98  --stdin                                 false
% 2.23/0.98  --stats_out                             all
% 2.23/0.98  
% 2.23/0.98  ------ General Options
% 2.23/0.98  
% 2.23/0.98  --fof                                   false
% 2.23/0.98  --time_out_real                         305.
% 2.23/0.98  --time_out_virtual                      -1.
% 2.23/0.98  --symbol_type_check                     false
% 2.23/0.98  --clausify_out                          false
% 2.23/0.98  --sig_cnt_out                           false
% 2.23/0.98  --trig_cnt_out                          false
% 2.23/0.98  --trig_cnt_out_tolerance                1.
% 2.23/0.98  --trig_cnt_out_sk_spl                   false
% 2.23/0.98  --abstr_cl_out                          false
% 2.23/0.98  
% 2.23/0.98  ------ Global Options
% 2.23/0.98  
% 2.23/0.98  --schedule                              default
% 2.23/0.98  --add_important_lit                     false
% 2.23/0.98  --prop_solver_per_cl                    1000
% 2.23/0.98  --min_unsat_core                        false
% 2.23/0.98  --soft_assumptions                      false
% 2.23/0.98  --soft_lemma_size                       3
% 2.23/0.98  --prop_impl_unit_size                   0
% 2.23/0.98  --prop_impl_unit                        []
% 2.23/0.98  --share_sel_clauses                     true
% 2.23/0.98  --reset_solvers                         false
% 2.23/0.98  --bc_imp_inh                            [conj_cone]
% 2.23/0.98  --conj_cone_tolerance                   3.
% 2.23/0.98  --extra_neg_conj                        none
% 2.23/0.98  --large_theory_mode                     true
% 2.23/0.98  --prolific_symb_bound                   200
% 2.23/0.98  --lt_threshold                          2000
% 2.23/0.98  --clause_weak_htbl                      true
% 2.23/0.98  --gc_record_bc_elim                     false
% 2.23/0.98  
% 2.23/0.98  ------ Preprocessing Options
% 2.23/0.98  
% 2.23/0.98  --preprocessing_flag                    true
% 2.23/0.98  --time_out_prep_mult                    0.1
% 2.23/0.98  --splitting_mode                        input
% 2.23/0.98  --splitting_grd                         true
% 2.23/0.98  --splitting_cvd                         false
% 2.23/0.98  --splitting_cvd_svl                     false
% 2.23/0.98  --splitting_nvd                         32
% 2.23/0.98  --sub_typing                            true
% 2.23/0.98  --prep_gs_sim                           true
% 2.23/0.98  --prep_unflatten                        true
% 2.23/0.98  --prep_res_sim                          true
% 2.23/0.98  --prep_upred                            true
% 2.23/0.98  --prep_sem_filter                       exhaustive
% 2.23/0.98  --prep_sem_filter_out                   false
% 2.23/0.98  --pred_elim                             true
% 2.23/0.98  --res_sim_input                         true
% 2.23/0.98  --eq_ax_congr_red                       true
% 2.23/0.98  --pure_diseq_elim                       true
% 2.23/0.98  --brand_transform                       false
% 2.23/0.98  --non_eq_to_eq                          false
% 2.23/0.98  --prep_def_merge                        true
% 2.23/0.98  --prep_def_merge_prop_impl              false
% 2.23/0.98  --prep_def_merge_mbd                    true
% 2.23/0.98  --prep_def_merge_tr_red                 false
% 2.23/0.98  --prep_def_merge_tr_cl                  false
% 2.23/0.98  --smt_preprocessing                     true
% 2.23/0.98  --smt_ac_axioms                         fast
% 2.23/0.98  --preprocessed_out                      false
% 2.23/0.98  --preprocessed_stats                    false
% 2.23/0.98  
% 2.23/0.98  ------ Abstraction refinement Options
% 2.23/0.98  
% 2.23/0.98  --abstr_ref                             []
% 2.23/0.98  --abstr_ref_prep                        false
% 2.23/0.98  --abstr_ref_until_sat                   false
% 2.23/0.98  --abstr_ref_sig_restrict                funpre
% 2.23/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.23/0.98  --abstr_ref_under                       []
% 2.23/0.98  
% 2.23/0.98  ------ SAT Options
% 2.23/0.98  
% 2.23/0.98  --sat_mode                              false
% 2.23/0.98  --sat_fm_restart_options                ""
% 2.23/0.98  --sat_gr_def                            false
% 2.23/0.98  --sat_epr_types                         true
% 2.23/0.98  --sat_non_cyclic_types                  false
% 2.23/0.98  --sat_finite_models                     false
% 2.23/0.98  --sat_fm_lemmas                         false
% 2.23/0.98  --sat_fm_prep                           false
% 2.23/0.98  --sat_fm_uc_incr                        true
% 2.23/0.98  --sat_out_model                         small
% 2.23/0.98  --sat_out_clauses                       false
% 2.23/0.98  
% 2.23/0.98  ------ QBF Options
% 2.23/0.98  
% 2.23/0.98  --qbf_mode                              false
% 2.23/0.98  --qbf_elim_univ                         false
% 2.23/0.98  --qbf_dom_inst                          none
% 2.23/0.98  --qbf_dom_pre_inst                      false
% 2.23/0.98  --qbf_sk_in                             false
% 2.23/0.98  --qbf_pred_elim                         true
% 2.23/0.98  --qbf_split                             512
% 2.23/0.98  
% 2.23/0.98  ------ BMC1 Options
% 2.23/0.98  
% 2.23/0.98  --bmc1_incremental                      false
% 2.23/0.98  --bmc1_axioms                           reachable_all
% 2.23/0.98  --bmc1_min_bound                        0
% 2.23/0.98  --bmc1_max_bound                        -1
% 2.23/0.98  --bmc1_max_bound_default                -1
% 2.23/0.98  --bmc1_symbol_reachability              true
% 2.23/0.98  --bmc1_property_lemmas                  false
% 2.23/0.98  --bmc1_k_induction                      false
% 2.23/0.98  --bmc1_non_equiv_states                 false
% 2.23/0.98  --bmc1_deadlock                         false
% 2.23/0.98  --bmc1_ucm                              false
% 2.23/0.98  --bmc1_add_unsat_core                   none
% 2.23/0.98  --bmc1_unsat_core_children              false
% 2.23/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.23/0.98  --bmc1_out_stat                         full
% 2.23/0.98  --bmc1_ground_init                      false
% 2.23/0.98  --bmc1_pre_inst_next_state              false
% 2.23/0.98  --bmc1_pre_inst_state                   false
% 2.23/0.98  --bmc1_pre_inst_reach_state             false
% 2.23/0.98  --bmc1_out_unsat_core                   false
% 2.23/0.98  --bmc1_aig_witness_out                  false
% 2.23/0.98  --bmc1_verbose                          false
% 2.23/0.98  --bmc1_dump_clauses_tptp                false
% 2.23/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.23/0.98  --bmc1_dump_file                        -
% 2.23/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.23/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.23/0.98  --bmc1_ucm_extend_mode                  1
% 2.23/0.98  --bmc1_ucm_init_mode                    2
% 2.23/0.98  --bmc1_ucm_cone_mode                    none
% 2.23/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.23/0.98  --bmc1_ucm_relax_model                  4
% 2.23/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.23/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.23/0.98  --bmc1_ucm_layered_model                none
% 2.23/0.98  --bmc1_ucm_max_lemma_size               10
% 2.23/0.98  
% 2.23/0.98  ------ AIG Options
% 2.23/0.98  
% 2.23/0.98  --aig_mode                              false
% 2.23/0.98  
% 2.23/0.98  ------ Instantiation Options
% 2.23/0.98  
% 2.23/0.98  --instantiation_flag                    true
% 2.23/0.98  --inst_sos_flag                         false
% 2.23/0.98  --inst_sos_phase                        true
% 2.23/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.23/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.23/0.98  --inst_lit_sel_side                     num_symb
% 2.23/0.98  --inst_solver_per_active                1400
% 2.23/0.98  --inst_solver_calls_frac                1.
% 2.23/0.98  --inst_passive_queue_type               priority_queues
% 2.23/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.23/0.98  --inst_passive_queues_freq              [25;2]
% 2.23/0.98  --inst_dismatching                      true
% 2.23/0.98  --inst_eager_unprocessed_to_passive     true
% 2.23/0.98  --inst_prop_sim_given                   true
% 2.23/0.98  --inst_prop_sim_new                     false
% 2.23/0.98  --inst_subs_new                         false
% 2.23/0.98  --inst_eq_res_simp                      false
% 2.23/0.98  --inst_subs_given                       false
% 2.23/0.98  --inst_orphan_elimination               true
% 2.23/0.98  --inst_learning_loop_flag               true
% 2.23/0.98  --inst_learning_start                   3000
% 2.23/0.98  --inst_learning_factor                  2
% 2.23/0.98  --inst_start_prop_sim_after_learn       3
% 2.23/0.98  --inst_sel_renew                        solver
% 2.23/0.98  --inst_lit_activity_flag                true
% 2.23/0.98  --inst_restr_to_given                   false
% 2.23/0.98  --inst_activity_threshold               500
% 2.23/0.98  --inst_out_proof                        true
% 2.23/0.98  
% 2.23/0.98  ------ Resolution Options
% 2.23/0.98  
% 2.23/0.98  --resolution_flag                       true
% 2.23/0.98  --res_lit_sel                           adaptive
% 2.23/0.98  --res_lit_sel_side                      none
% 2.23/0.98  --res_ordering                          kbo
% 2.23/0.98  --res_to_prop_solver                    active
% 2.23/0.98  --res_prop_simpl_new                    false
% 2.23/0.98  --res_prop_simpl_given                  true
% 2.23/0.98  --res_passive_queue_type                priority_queues
% 2.23/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.23/0.98  --res_passive_queues_freq               [15;5]
% 2.23/0.98  --res_forward_subs                      full
% 2.23/0.98  --res_backward_subs                     full
% 2.23/0.98  --res_forward_subs_resolution           true
% 2.23/0.98  --res_backward_subs_resolution          true
% 2.23/0.98  --res_orphan_elimination                true
% 2.23/0.98  --res_time_limit                        2.
% 2.23/0.98  --res_out_proof                         true
% 2.23/0.98  
% 2.23/0.98  ------ Superposition Options
% 2.23/0.98  
% 2.23/0.98  --superposition_flag                    true
% 2.23/0.98  --sup_passive_queue_type                priority_queues
% 2.23/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.23/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.23/0.98  --demod_completeness_check              fast
% 2.23/0.98  --demod_use_ground                      true
% 2.23/0.98  --sup_to_prop_solver                    passive
% 2.23/0.98  --sup_prop_simpl_new                    true
% 2.23/0.98  --sup_prop_simpl_given                  true
% 2.23/0.98  --sup_fun_splitting                     false
% 2.23/0.98  --sup_smt_interval                      50000
% 2.23/0.98  
% 2.23/0.98  ------ Superposition Simplification Setup
% 2.23/0.98  
% 2.23/0.98  --sup_indices_passive                   []
% 2.23/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.23/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.98  --sup_full_bw                           [BwDemod]
% 2.23/0.98  --sup_immed_triv                        [TrivRules]
% 2.23/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.23/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.98  --sup_immed_bw_main                     []
% 2.23/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.23/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/0.98  
% 2.23/0.98  ------ Combination Options
% 2.23/0.98  
% 2.23/0.98  --comb_res_mult                         3
% 2.23/0.98  --comb_sup_mult                         2
% 2.23/0.98  --comb_inst_mult                        10
% 2.23/0.98  
% 2.23/0.98  ------ Debug Options
% 2.23/0.98  
% 2.23/0.98  --dbg_backtrace                         false
% 2.23/0.98  --dbg_dump_prop_clauses                 false
% 2.23/0.98  --dbg_dump_prop_clauses_file            -
% 2.23/0.98  --dbg_out_stat                          false
% 2.23/0.98  ------ Parsing...
% 2.23/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.23/0.98  
% 2.23/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.23/0.98  
% 2.23/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.23/0.98  
% 2.23/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.23/0.98  ------ Proving...
% 2.23/0.98  ------ Problem Properties 
% 2.23/0.98  
% 2.23/0.98  
% 2.23/0.98  clauses                                 28
% 2.23/0.98  conjectures                             18
% 2.23/0.98  EPR                                     16
% 2.23/0.98  Horn                                    21
% 2.23/0.98  unary                                   16
% 2.23/0.98  binary                                  2
% 2.23/0.98  lits                                    108
% 2.23/0.98  lits eq                                 11
% 2.23/0.98  fd_pure                                 0
% 2.23/0.98  fd_pseudo                               0
% 2.23/0.98  fd_cond                                 0
% 2.23/0.98  fd_pseudo_cond                          0
% 2.23/0.98  AC symbols                              0
% 2.23/0.98  
% 2.23/0.98  ------ Schedule dynamic 5 is on 
% 2.23/0.98  
% 2.23/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.23/0.98  
% 2.23/0.98  
% 2.23/0.98  ------ 
% 2.23/0.98  Current options:
% 2.23/0.98  ------ 
% 2.23/0.98  
% 2.23/0.98  ------ Input Options
% 2.23/0.98  
% 2.23/0.98  --out_options                           all
% 2.23/0.98  --tptp_safe_out                         true
% 2.23/0.98  --problem_path                          ""
% 2.23/0.98  --include_path                          ""
% 2.23/0.98  --clausifier                            res/vclausify_rel
% 2.23/0.98  --clausifier_options                    --mode clausify
% 2.23/0.98  --stdin                                 false
% 2.23/0.98  --stats_out                             all
% 2.23/0.98  
% 2.23/0.98  ------ General Options
% 2.23/0.98  
% 2.23/0.98  --fof                                   false
% 2.23/0.98  --time_out_real                         305.
% 2.23/0.98  --time_out_virtual                      -1.
% 2.23/0.98  --symbol_type_check                     false
% 2.23/0.98  --clausify_out                          false
% 2.23/0.98  --sig_cnt_out                           false
% 2.23/0.98  --trig_cnt_out                          false
% 2.23/0.98  --trig_cnt_out_tolerance                1.
% 2.23/0.98  --trig_cnt_out_sk_spl                   false
% 2.23/0.98  --abstr_cl_out                          false
% 2.23/0.98  
% 2.23/0.98  ------ Global Options
% 2.23/0.98  
% 2.23/0.98  --schedule                              default
% 2.23/0.98  --add_important_lit                     false
% 2.23/0.98  --prop_solver_per_cl                    1000
% 2.23/0.98  --min_unsat_core                        false
% 2.23/0.98  --soft_assumptions                      false
% 2.23/0.98  --soft_lemma_size                       3
% 2.23/0.98  --prop_impl_unit_size                   0
% 2.23/0.98  --prop_impl_unit                        []
% 2.23/0.98  --share_sel_clauses                     true
% 2.23/0.98  --reset_solvers                         false
% 2.23/0.98  --bc_imp_inh                            [conj_cone]
% 2.23/0.98  --conj_cone_tolerance                   3.
% 2.23/0.98  --extra_neg_conj                        none
% 2.23/0.98  --large_theory_mode                     true
% 2.23/0.98  --prolific_symb_bound                   200
% 2.23/0.98  --lt_threshold                          2000
% 2.23/0.98  --clause_weak_htbl                      true
% 2.23/0.98  --gc_record_bc_elim                     false
% 2.23/0.98  
% 2.23/0.98  ------ Preprocessing Options
% 2.23/0.98  
% 2.23/0.98  --preprocessing_flag                    true
% 2.23/0.98  --time_out_prep_mult                    0.1
% 2.23/0.98  --splitting_mode                        input
% 2.23/0.98  --splitting_grd                         true
% 2.23/0.98  --splitting_cvd                         false
% 2.23/0.98  --splitting_cvd_svl                     false
% 2.23/0.98  --splitting_nvd                         32
% 2.23/0.98  --sub_typing                            true
% 2.23/0.98  --prep_gs_sim                           true
% 2.23/0.98  --prep_unflatten                        true
% 2.23/0.98  --prep_res_sim                          true
% 2.23/0.98  --prep_upred                            true
% 2.23/0.98  --prep_sem_filter                       exhaustive
% 2.23/0.98  --prep_sem_filter_out                   false
% 2.23/0.98  --pred_elim                             true
% 2.23/0.98  --res_sim_input                         true
% 2.23/0.98  --eq_ax_congr_red                       true
% 2.23/0.98  --pure_diseq_elim                       true
% 2.23/0.98  --brand_transform                       false
% 2.23/0.98  --non_eq_to_eq                          false
% 2.23/0.98  --prep_def_merge                        true
% 2.23/0.98  --prep_def_merge_prop_impl              false
% 2.23/0.98  --prep_def_merge_mbd                    true
% 2.23/0.98  --prep_def_merge_tr_red                 false
% 2.23/0.98  --prep_def_merge_tr_cl                  false
% 2.23/0.98  --smt_preprocessing                     true
% 2.23/0.98  --smt_ac_axioms                         fast
% 2.23/0.98  --preprocessed_out                      false
% 2.23/0.98  --preprocessed_stats                    false
% 2.23/0.98  
% 2.23/0.98  ------ Abstraction refinement Options
% 2.23/0.98  
% 2.23/0.98  --abstr_ref                             []
% 2.23/0.98  --abstr_ref_prep                        false
% 2.23/0.98  --abstr_ref_until_sat                   false
% 2.23/0.98  --abstr_ref_sig_restrict                funpre
% 2.23/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.23/0.98  --abstr_ref_under                       []
% 2.23/0.98  
% 2.23/0.98  ------ SAT Options
% 2.23/0.98  
% 2.23/0.98  --sat_mode                              false
% 2.23/0.98  --sat_fm_restart_options                ""
% 2.23/0.98  --sat_gr_def                            false
% 2.23/0.98  --sat_epr_types                         true
% 2.23/0.98  --sat_non_cyclic_types                  false
% 2.23/0.98  --sat_finite_models                     false
% 2.23/0.98  --sat_fm_lemmas                         false
% 2.23/0.98  --sat_fm_prep                           false
% 2.23/0.98  --sat_fm_uc_incr                        true
% 2.23/0.98  --sat_out_model                         small
% 2.23/0.98  --sat_out_clauses                       false
% 2.23/0.98  
% 2.23/0.98  ------ QBF Options
% 2.23/0.98  
% 2.23/0.98  --qbf_mode                              false
% 2.23/0.98  --qbf_elim_univ                         false
% 2.23/0.98  --qbf_dom_inst                          none
% 2.23/0.98  --qbf_dom_pre_inst                      false
% 2.23/0.98  --qbf_sk_in                             false
% 2.23/0.98  --qbf_pred_elim                         true
% 2.23/0.98  --qbf_split                             512
% 2.23/0.98  
% 2.23/0.98  ------ BMC1 Options
% 2.23/0.98  
% 2.23/0.98  --bmc1_incremental                      false
% 2.23/0.98  --bmc1_axioms                           reachable_all
% 2.23/0.98  --bmc1_min_bound                        0
% 2.23/0.98  --bmc1_max_bound                        -1
% 2.23/0.98  --bmc1_max_bound_default                -1
% 2.23/0.98  --bmc1_symbol_reachability              true
% 2.23/0.98  --bmc1_property_lemmas                  false
% 2.23/0.98  --bmc1_k_induction                      false
% 2.23/0.98  --bmc1_non_equiv_states                 false
% 2.23/0.98  --bmc1_deadlock                         false
% 2.23/0.98  --bmc1_ucm                              false
% 2.23/0.98  --bmc1_add_unsat_core                   none
% 2.23/0.98  --bmc1_unsat_core_children              false
% 2.23/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.23/0.98  --bmc1_out_stat                         full
% 2.23/0.98  --bmc1_ground_init                      false
% 2.23/0.98  --bmc1_pre_inst_next_state              false
% 2.23/0.98  --bmc1_pre_inst_state                   false
% 2.23/0.98  --bmc1_pre_inst_reach_state             false
% 2.23/0.98  --bmc1_out_unsat_core                   false
% 2.23/0.98  --bmc1_aig_witness_out                  false
% 2.23/0.98  --bmc1_verbose                          false
% 2.23/0.98  --bmc1_dump_clauses_tptp                false
% 2.23/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.23/0.98  --bmc1_dump_file                        -
% 2.23/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.23/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.23/0.98  --bmc1_ucm_extend_mode                  1
% 2.23/0.98  --bmc1_ucm_init_mode                    2
% 2.23/0.98  --bmc1_ucm_cone_mode                    none
% 2.23/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.23/0.98  --bmc1_ucm_relax_model                  4
% 2.23/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.23/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.23/0.98  --bmc1_ucm_layered_model                none
% 2.23/0.98  --bmc1_ucm_max_lemma_size               10
% 2.23/0.98  
% 2.23/0.98  ------ AIG Options
% 2.23/0.98  
% 2.23/0.98  --aig_mode                              false
% 2.23/0.98  
% 2.23/0.98  ------ Instantiation Options
% 2.23/0.98  
% 2.23/0.98  --instantiation_flag                    true
% 2.23/0.98  --inst_sos_flag                         false
% 2.23/0.98  --inst_sos_phase                        true
% 2.23/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.23/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.23/0.98  --inst_lit_sel_side                     none
% 2.23/0.98  --inst_solver_per_active                1400
% 2.23/0.98  --inst_solver_calls_frac                1.
% 2.23/0.98  --inst_passive_queue_type               priority_queues
% 2.23/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.23/0.98  --inst_passive_queues_freq              [25;2]
% 2.23/0.98  --inst_dismatching                      true
% 2.23/0.98  --inst_eager_unprocessed_to_passive     true
% 2.23/0.98  --inst_prop_sim_given                   true
% 2.23/0.98  --inst_prop_sim_new                     false
% 2.23/0.98  --inst_subs_new                         false
% 2.23/0.98  --inst_eq_res_simp                      false
% 2.23/0.98  --inst_subs_given                       false
% 2.23/0.98  --inst_orphan_elimination               true
% 2.23/0.98  --inst_learning_loop_flag               true
% 2.23/0.98  --inst_learning_start                   3000
% 2.23/0.98  --inst_learning_factor                  2
% 2.23/0.98  --inst_start_prop_sim_after_learn       3
% 2.23/0.98  --inst_sel_renew                        solver
% 2.23/0.98  --inst_lit_activity_flag                true
% 2.23/0.98  --inst_restr_to_given                   false
% 2.23/0.98  --inst_activity_threshold               500
% 2.23/0.98  --inst_out_proof                        true
% 2.23/0.98  
% 2.23/0.98  ------ Resolution Options
% 2.23/0.98  
% 2.23/0.98  --resolution_flag                       false
% 2.23/0.98  --res_lit_sel                           adaptive
% 2.23/0.98  --res_lit_sel_side                      none
% 2.23/0.98  --res_ordering                          kbo
% 2.23/0.98  --res_to_prop_solver                    active
% 2.23/0.98  --res_prop_simpl_new                    false
% 2.23/0.98  --res_prop_simpl_given                  true
% 2.23/0.98  --res_passive_queue_type                priority_queues
% 2.23/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.23/0.98  --res_passive_queues_freq               [15;5]
% 2.23/0.98  --res_forward_subs                      full
% 2.23/0.98  --res_backward_subs                     full
% 2.23/0.98  --res_forward_subs_resolution           true
% 2.23/0.98  --res_backward_subs_resolution          true
% 2.23/0.98  --res_orphan_elimination                true
% 2.23/0.98  --res_time_limit                        2.
% 2.23/0.98  --res_out_proof                         true
% 2.23/0.98  
% 2.23/0.98  ------ Superposition Options
% 2.23/0.98  
% 2.23/0.98  --superposition_flag                    true
% 2.23/0.98  --sup_passive_queue_type                priority_queues
% 2.23/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.23/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.23/0.98  --demod_completeness_check              fast
% 2.23/0.98  --demod_use_ground                      true
% 2.23/0.98  --sup_to_prop_solver                    passive
% 2.23/0.98  --sup_prop_simpl_new                    true
% 2.23/0.98  --sup_prop_simpl_given                  true
% 2.23/0.98  --sup_fun_splitting                     false
% 2.23/0.98  --sup_smt_interval                      50000
% 2.23/0.98  
% 2.23/0.98  ------ Superposition Simplification Setup
% 2.23/0.98  
% 2.23/0.98  --sup_indices_passive                   []
% 2.23/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.23/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.98  --sup_full_bw                           [BwDemod]
% 2.23/0.98  --sup_immed_triv                        [TrivRules]
% 2.23/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.23/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.98  --sup_immed_bw_main                     []
% 2.23/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.23/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/0.98  
% 2.23/0.98  ------ Combination Options
% 2.23/0.98  
% 2.23/0.98  --comb_res_mult                         3
% 2.23/0.98  --comb_sup_mult                         2
% 2.23/0.98  --comb_inst_mult                        10
% 2.23/0.98  
% 2.23/0.98  ------ Debug Options
% 2.23/0.98  
% 2.23/0.98  --dbg_backtrace                         false
% 2.23/0.98  --dbg_dump_prop_clauses                 false
% 2.23/0.98  --dbg_dump_prop_clauses_file            -
% 2.23/0.98  --dbg_out_stat                          false
% 2.23/0.98  
% 2.23/0.98  
% 2.23/0.98  
% 2.23/0.98  
% 2.23/0.98  ------ Proving...
% 2.23/0.98  
% 2.23/0.98  
% 2.23/0.98  % SZS status Theorem for theBenchmark.p
% 2.23/0.98  
% 2.23/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.23/0.98  
% 2.23/0.98  fof(f10,conjecture,(
% 2.23/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 2.23/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.98  
% 2.23/0.98  fof(f11,negated_conjecture,(
% 2.23/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 2.23/0.98    inference(negated_conjecture,[],[f10])).
% 2.23/0.98  
% 2.23/0.98  fof(f28,plain,(
% 2.23/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.23/0.98    inference(ennf_transformation,[],[f11])).
% 2.23/0.98  
% 2.23/0.98  fof(f29,plain,(
% 2.23/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.23/0.98    inference(flattening,[],[f28])).
% 2.23/0.98  
% 2.23/0.98  fof(f31,plain,(
% 2.23/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.23/0.98    inference(nnf_transformation,[],[f29])).
% 2.23/0.98  
% 2.23/0.98  fof(f32,plain,(
% 2.23/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.23/0.98    inference(flattening,[],[f31])).
% 2.23/0.98  
% 2.23/0.98  fof(f39,plain,(
% 2.23/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6) | r1_tmap_1(X3,X0,X4,X5)) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 2.23/0.98    introduced(choice_axiom,[])).
% 2.23/0.98  
% 2.23/0.98  fof(f38,plain,(
% 2.23/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,sK5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 2.23/0.98    introduced(choice_axiom,[])).
% 2.23/0.98  
% 2.23/0.98  fof(f37,plain,(
% 2.23/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6) | ~r1_tmap_1(X3,X0,sK4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6) | r1_tmap_1(X3,X0,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 2.23/0.98    introduced(choice_axiom,[])).
% 2.23/0.98  
% 2.23/0.98  fof(f36,plain,(
% 2.23/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6) | ~r1_tmap_1(sK3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6) | r1_tmap_1(sK3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(X2,sK3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 2.23/0.98    introduced(choice_axiom,[])).
% 2.23/0.98  
% 2.23/0.98  fof(f35,plain,(
% 2.23/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK2,X1) & v1_tsep_1(sK2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 2.23/0.98    introduced(choice_axiom,[])).
% 2.23/0.98  
% 2.23/0.98  fof(f34,plain,(
% 2.23/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK1) & v1_tsep_1(X2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.23/0.98    introduced(choice_axiom,[])).
% 2.23/0.98  
% 2.23/0.98  fof(f33,plain,(
% 2.23/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.23/0.98    introduced(choice_axiom,[])).
% 2.23/0.98  
% 2.23/0.98  fof(f40,plain,(
% 2.23/0.98    (((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.23/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f32,f39,f38,f37,f36,f35,f34,f33])).
% 2.23/0.98  
% 2.23/0.98  fof(f61,plain,(
% 2.23/0.98    m1_pre_topc(sK3,sK1)),
% 2.23/0.98    inference(cnf_transformation,[],[f40])).
% 2.23/0.98  
% 2.23/0.98  fof(f67,plain,(
% 2.23/0.98    m1_pre_topc(sK2,sK3)),
% 2.23/0.98    inference(cnf_transformation,[],[f40])).
% 2.23/0.98  
% 2.23/0.98  fof(f5,axiom,(
% 2.23/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.23/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.98  
% 2.23/0.98  fof(f19,plain,(
% 2.23/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.98    inference(ennf_transformation,[],[f5])).
% 2.23/0.98  
% 2.23/0.98  fof(f20,plain,(
% 2.23/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.98    inference(flattening,[],[f19])).
% 2.23/0.98  
% 2.23/0.98  fof(f45,plain,(
% 2.23/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.99    inference(cnf_transformation,[],[f20])).
% 2.23/0.99  
% 2.23/0.99  fof(f63,plain,(
% 2.23/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f62,plain,(
% 2.23/0.99    v1_funct_1(sK4)),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f9,axiom,(
% 2.23/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.23/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.99  
% 2.23/0.99  fof(f26,plain,(
% 2.23/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.23/0.99    inference(ennf_transformation,[],[f9])).
% 2.23/0.99  
% 2.23/0.99  fof(f27,plain,(
% 2.23/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.23/0.99    inference(flattening,[],[f26])).
% 2.23/0.99  
% 2.23/0.99  fof(f51,plain,(
% 2.23/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.23/0.99    inference(cnf_transformation,[],[f27])).
% 2.23/0.99  
% 2.23/0.99  fof(f52,plain,(
% 2.23/0.99    ~v2_struct_0(sK0)),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f53,plain,(
% 2.23/0.99    v2_pre_topc(sK0)),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f54,plain,(
% 2.23/0.99    l1_pre_topc(sK0)),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f64,plain,(
% 2.23/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f4,axiom,(
% 2.23/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.23/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.99  
% 2.23/0.99  fof(f17,plain,(
% 2.23/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.99    inference(ennf_transformation,[],[f4])).
% 2.23/0.99  
% 2.23/0.99  fof(f18,plain,(
% 2.23/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.99    inference(flattening,[],[f17])).
% 2.23/0.99  
% 2.23/0.99  fof(f44,plain,(
% 2.23/0.99    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.99    inference(cnf_transformation,[],[f18])).
% 2.23/0.99  
% 2.23/0.99  fof(f56,plain,(
% 2.23/0.99    v2_pre_topc(sK1)),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f57,plain,(
% 2.23/0.99    l1_pre_topc(sK1)),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f60,plain,(
% 2.23/0.99    ~v2_struct_0(sK3)),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f2,axiom,(
% 2.23/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.23/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.99  
% 2.23/0.99  fof(f14,plain,(
% 2.23/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.23/0.99    inference(ennf_transformation,[],[f2])).
% 2.23/0.99  
% 2.23/0.99  fof(f15,plain,(
% 2.23/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.23/0.99    inference(flattening,[],[f14])).
% 2.23/0.99  
% 2.23/0.99  fof(f42,plain,(
% 2.23/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.23/0.99    inference(cnf_transformation,[],[f15])).
% 2.23/0.99  
% 2.23/0.99  fof(f3,axiom,(
% 2.23/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.23/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.99  
% 2.23/0.99  fof(f16,plain,(
% 2.23/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.23/0.99    inference(ennf_transformation,[],[f3])).
% 2.23/0.99  
% 2.23/0.99  fof(f43,plain,(
% 2.23/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.23/0.99    inference(cnf_transformation,[],[f16])).
% 2.23/0.99  
% 2.23/0.99  fof(f55,plain,(
% 2.23/0.99    ~v2_struct_0(sK1)),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f72,plain,(
% 2.23/0.99    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f70,plain,(
% 2.23/0.99    sK5 = sK6),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f71,plain,(
% 2.23/0.99    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f8,axiom,(
% 2.23/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.23/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.99  
% 2.23/0.99  fof(f24,plain,(
% 2.23/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.99    inference(ennf_transformation,[],[f8])).
% 2.23/0.99  
% 2.23/0.99  fof(f25,plain,(
% 2.23/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.99    inference(flattening,[],[f24])).
% 2.23/0.99  
% 2.23/0.99  fof(f30,plain,(
% 2.23/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4))) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.99    inference(nnf_transformation,[],[f25])).
% 2.23/0.99  
% 2.23/0.99  fof(f49,plain,(
% 2.23/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.99    inference(cnf_transformation,[],[f30])).
% 2.23/0.99  
% 2.23/0.99  fof(f74,plain,(
% 2.23/0.99    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.99    inference(equality_resolution,[],[f49])).
% 2.23/0.99  
% 2.23/0.99  fof(f50,plain,(
% 2.23/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.99    inference(cnf_transformation,[],[f30])).
% 2.23/0.99  
% 2.23/0.99  fof(f73,plain,(
% 2.23/0.99    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.99    inference(equality_resolution,[],[f50])).
% 2.23/0.99  
% 2.23/0.99  fof(f1,axiom,(
% 2.23/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.23/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.99  
% 2.23/0.99  fof(f12,plain,(
% 2.23/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.23/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 2.23/0.99  
% 2.23/0.99  fof(f13,plain,(
% 2.23/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.23/0.99    inference(ennf_transformation,[],[f12])).
% 2.23/0.99  
% 2.23/0.99  fof(f41,plain,(
% 2.23/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.23/0.99    inference(cnf_transformation,[],[f13])).
% 2.23/0.99  
% 2.23/0.99  fof(f6,axiom,(
% 2.23/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 2.23/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.99  
% 2.23/0.99  fof(f21,plain,(
% 2.23/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.99    inference(ennf_transformation,[],[f6])).
% 2.23/0.99  
% 2.23/0.99  fof(f22,plain,(
% 2.23/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.99    inference(flattening,[],[f21])).
% 2.23/0.99  
% 2.23/0.99  fof(f46,plain,(
% 2.23/0.99    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.99    inference(cnf_transformation,[],[f22])).
% 2.23/0.99  
% 2.23/0.99  fof(f7,axiom,(
% 2.23/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.23/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.99  
% 2.23/0.99  fof(f23,plain,(
% 2.23/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.23/0.99    inference(ennf_transformation,[],[f7])).
% 2.23/0.99  
% 2.23/0.99  fof(f48,plain,(
% 2.23/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.23/0.99    inference(cnf_transformation,[],[f23])).
% 2.23/0.99  
% 2.23/0.99  fof(f68,plain,(
% 2.23/0.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f69,plain,(
% 2.23/0.99    m1_subset_1(sK6,u1_struct_0(sK2))),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f65,plain,(
% 2.23/0.99    v1_tsep_1(sK2,sK1)),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f59,plain,(
% 2.23/0.99    m1_pre_topc(sK2,sK1)),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  fof(f58,plain,(
% 2.23/0.99    ~v2_struct_0(sK2)),
% 2.23/0.99    inference(cnf_transformation,[],[f40])).
% 2.23/0.99  
% 2.23/0.99  cnf(c_22,negated_conjecture,
% 2.23/0.99      ( m1_pre_topc(sK3,sK1) ),
% 2.23/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_943,negated_conjecture,
% 2.23/0.99      ( m1_pre_topc(sK3,sK1) ),
% 2.23/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1573,plain,
% 2.23/0.99      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_943]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_16,negated_conjecture,
% 2.23/0.99      ( m1_pre_topc(sK2,sK3) ),
% 2.23/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_947,negated_conjecture,
% 2.23/0.99      ( m1_pre_topc(sK2,sK3) ),
% 2.23/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1569,plain,
% 2.23/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_4,plain,
% 2.23/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.23/0.99      | ~ m1_pre_topc(X3,X4)
% 2.23/0.99      | ~ m1_pre_topc(X3,X1)
% 2.23/0.99      | ~ m1_pre_topc(X1,X4)
% 2.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.23/0.99      | v2_struct_0(X4)
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | ~ v1_funct_1(X0)
% 2.23/0.99      | ~ l1_pre_topc(X4)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X4)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.23/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_20,negated_conjecture,
% 2.23/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
% 2.23/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_583,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.23/0.99      | ~ m1_pre_topc(X0,X2)
% 2.23/0.99      | ~ m1_pre_topc(X1,X2)
% 2.23/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 2.23/0.99      | v2_struct_0(X4)
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | ~ v1_funct_1(X3)
% 2.23/0.99      | ~ l1_pre_topc(X4)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X4)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X4) != u1_struct_0(sK0)
% 2.23/0.99      | sK4 != X3 ),
% 2.23/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_20]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_584,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.23/0.99      | ~ m1_pre_topc(X0,X2)
% 2.23/0.99      | ~ m1_pre_topc(X1,X2)
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | v2_struct_0(X3)
% 2.23/0.99      | ~ v1_funct_1(sK4)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ l1_pre_topc(X3)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X3)
% 2.23/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X3) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(unflattening,[status(thm)],[c_583]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_21,negated_conjecture,
% 2.23/0.99      ( v1_funct_1(sK4) ),
% 2.23/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_588,plain,
% 2.23/0.99      ( v2_struct_0(X3)
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.23/0.99      | ~ m1_pre_topc(X1,X2)
% 2.23/0.99      | ~ m1_pre_topc(X0,X2)
% 2.23/0.99      | ~ m1_pre_topc(X0,X1)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ l1_pre_topc(X3)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X3)
% 2.23/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X3) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(global_propositional_subsumption,
% 2.23/0.99                [status(thm)],
% 2.23/0.99                [c_584,c_21]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_589,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.23/0.99      | ~ m1_pre_topc(X0,X2)
% 2.23/0.99      | ~ m1_pre_topc(X1,X2)
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | v2_struct_0(X3)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ l1_pre_topc(X3)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X3)
% 2.23/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X3) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(renaming,[status(thm)],[c_588]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_10,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.23/0.99      | ~ m1_pre_topc(X2,X0)
% 2.23/0.99      | m1_pre_topc(X2,X1)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X1) ),
% 2.23/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_620,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.23/0.99      | ~ m1_pre_topc(X1,X2)
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | v2_struct_0(X3)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ l1_pre_topc(X3)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X3)
% 2.23/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X3) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(forward_subsumption_resolution,
% 2.23/0.99                [status(thm)],
% 2.23/0.99                [c_589,c_10]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_930,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.23/0.99      | ~ m1_pre_topc(X1_51,X2_51)
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_51),u1_struct_0(X3_51))))
% 2.23/0.99      | v2_struct_0(X2_51)
% 2.23/0.99      | v2_struct_0(X3_51)
% 2.23/0.99      | ~ l1_pre_topc(X2_51)
% 2.23/0.99      | ~ l1_pre_topc(X3_51)
% 2.23/0.99      | ~ v2_pre_topc(X2_51)
% 2.23/0.99      | ~ v2_pre_topc(X3_51)
% 2.23/0.99      | k2_partfun1(u1_struct_0(X1_51),u1_struct_0(X3_51),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X2_51,X3_51,X1_51,X0_51,sK4)
% 2.23/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X3_51) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(subtyping,[status(esa)],[c_620]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1586,plain,
% 2.23/0.99      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK4,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,sK4)
% 2.23/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK0)
% 2.23/0.99      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 2.23/0.99      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 2.23/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 2.23/0.99      | v2_struct_0(X3_51) = iProver_top
% 2.23/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.23/0.99      | l1_pre_topc(X1_51) != iProver_top
% 2.23/0.99      | l1_pre_topc(X3_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(X1_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(X3_51) != iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_930]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3079,plain,
% 2.23/0.99      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK0),sK4,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK0,X0_51,X1_51,sK4)
% 2.23/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK3)
% 2.23/0.99      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.23/0.99      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.23/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
% 2.23/0.99      | v2_struct_0(X2_51) = iProver_top
% 2.23/0.99      | v2_struct_0(sK0) = iProver_top
% 2.23/0.99      | l1_pre_topc(X2_51) != iProver_top
% 2.23/0.99      | l1_pre_topc(sK0) != iProver_top
% 2.23/0.99      | v2_pre_topc(X2_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 2.23/0.99      inference(equality_resolution,[status(thm)],[c_1586]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_31,negated_conjecture,
% 2.23/0.99      ( ~ v2_struct_0(sK0) ),
% 2.23/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_32,plain,
% 2.23/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_30,negated_conjecture,
% 2.23/0.99      ( v2_pre_topc(sK0) ),
% 2.23/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_33,plain,
% 2.23/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_29,negated_conjecture,
% 2.23/0.99      ( l1_pre_topc(sK0) ),
% 2.23/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_34,plain,
% 2.23/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3270,plain,
% 2.23/0.99      ( v2_pre_topc(X2_51) != iProver_top
% 2.23/0.99      | v2_struct_0(X2_51) = iProver_top
% 2.23/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
% 2.23/0.99      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.23/0.99      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.23/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK3)
% 2.23/0.99      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK0),sK4,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK0,X0_51,X1_51,sK4)
% 2.23/0.99      | l1_pre_topc(X2_51) != iProver_top ),
% 2.23/0.99      inference(global_propositional_subsumption,
% 2.23/0.99                [status(thm)],
% 2.23/0.99                [c_3079,c_32,c_33,c_34]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3271,plain,
% 2.23/0.99      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK0),sK4,u1_struct_0(X1_51)) = k3_tmap_1(X2_51,sK0,X0_51,X1_51,sK4)
% 2.23/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK3)
% 2.23/0.99      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 2.23/0.99      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.23/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
% 2.23/0.99      | v2_struct_0(X2_51) = iProver_top
% 2.23/0.99      | l1_pre_topc(X2_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(X2_51) != iProver_top ),
% 2.23/0.99      inference(renaming,[status(thm)],[c_3270]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3282,plain,
% 2.23/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK0,sK3,X0_51,sK4)
% 2.23/0.99      | m1_pre_topc(X0_51,sK3) != iProver_top
% 2.23/0.99      | m1_pre_topc(sK3,X1_51) != iProver_top
% 2.23/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 2.23/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.23/0.99      | l1_pre_topc(X1_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(X1_51) != iProver_top ),
% 2.23/0.99      inference(equality_resolution,[status(thm)],[c_3271]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_19,negated_conjecture,
% 2.23/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
% 2.23/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_44,plain,
% 2.23/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3309,plain,
% 2.23/0.99      ( m1_pre_topc(sK3,X1_51) != iProver_top
% 2.23/0.99      | m1_pre_topc(X0_51,sK3) != iProver_top
% 2.23/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK0,sK3,X0_51,sK4)
% 2.23/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.23/0.99      | l1_pre_topc(X1_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(X1_51) != iProver_top ),
% 2.23/0.99      inference(global_propositional_subsumption,
% 2.23/0.99                [status(thm)],
% 2.23/0.99                [c_3282,c_44]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3310,plain,
% 2.23/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK0,sK3,X0_51,sK4)
% 2.23/0.99      | m1_pre_topc(X0_51,sK3) != iProver_top
% 2.23/0.99      | m1_pre_topc(sK3,X1_51) != iProver_top
% 2.23/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.23/0.99      | l1_pre_topc(X1_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(X1_51) != iProver_top ),
% 2.23/0.99      inference(renaming,[status(thm)],[c_3309]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3321,plain,
% 2.23/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0_51,sK0,sK3,sK2,sK4)
% 2.23/0.99      | m1_pre_topc(sK3,X0_51) != iProver_top
% 2.23/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.23/0.99      | l1_pre_topc(X0_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(X0_51) != iProver_top ),
% 2.23/0.99      inference(superposition,[status(thm)],[c_1569,c_3310]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3,plain,
% 2.23/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.23/0.99      | ~ m1_pre_topc(X3,X1)
% 2.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | ~ v1_funct_1(X0)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.23/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_634,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.23/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X3)
% 2.23/0.99      | ~ v1_funct_1(X2)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ l1_pre_topc(X3)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X3)
% 2.23/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X3) != u1_struct_0(sK0)
% 2.23/0.99      | sK4 != X2 ),
% 2.23/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_20]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_635,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | ~ v1_funct_1(sK4)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X2) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(unflattening,[status(thm)],[c_634]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_639,plain,
% 2.23/0.99      ( v2_struct_0(X2)
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.23/0.99      | ~ m1_pre_topc(X0,X1)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X2) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(global_propositional_subsumption,
% 2.23/0.99                [status(thm)],
% 2.23/0.99                [c_635,c_21]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_640,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X2) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(renaming,[status(thm)],[c_639]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_929,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_51),u1_struct_0(X2_51))))
% 2.23/0.99      | v2_struct_0(X1_51)
% 2.23/0.99      | v2_struct_0(X2_51)
% 2.23/0.99      | ~ l1_pre_topc(X1_51)
% 2.23/0.99      | ~ l1_pre_topc(X2_51)
% 2.23/0.99      | ~ v2_pre_topc(X1_51)
% 2.23/0.99      | ~ v2_pre_topc(X2_51)
% 2.23/0.99      | k2_partfun1(u1_struct_0(X1_51),u1_struct_0(X2_51),sK4,u1_struct_0(X0_51)) = k2_tmap_1(X1_51,X2_51,sK4,X0_51)
% 2.23/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X2_51) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(subtyping,[status(esa)],[c_640]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1587,plain,
% 2.23/0.99      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),sK4,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,sK4,X2_51)
% 2.23/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK0)
% 2.23/0.99      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 2.23/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 2.23/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.23/0.99      | v2_struct_0(X1_51) = iProver_top
% 2.23/0.99      | l1_pre_topc(X0_51) != iProver_top
% 2.23/0.99      | l1_pre_topc(X1_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(X0_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(X1_51) != iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_929]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2656,plain,
% 2.23/0.99      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK0),sK4,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK0,sK4,X1_51)
% 2.23/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK3)
% 2.23/0.99      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.23/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
% 2.23/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.23/0.99      | v2_struct_0(sK0) = iProver_top
% 2.23/0.99      | l1_pre_topc(X0_51) != iProver_top
% 2.23/0.99      | l1_pre_topc(sK0) != iProver_top
% 2.23/0.99      | v2_pre_topc(X0_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 2.23/0.99      inference(equality_resolution,[status(thm)],[c_1587]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3051,plain,
% 2.23/0.99      ( v2_pre_topc(X0_51) != iProver_top
% 2.23/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.23/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
% 2.23/0.99      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.23/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK3)
% 2.23/0.99      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK0),sK4,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK0,sK4,X1_51)
% 2.23/0.99      | l1_pre_topc(X0_51) != iProver_top ),
% 2.23/0.99      inference(global_propositional_subsumption,
% 2.23/0.99                [status(thm)],
% 2.23/0.99                [c_2656,c_32,c_33,c_34]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3052,plain,
% 2.23/0.99      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK0),sK4,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK0,sK4,X1_51)
% 2.23/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK3)
% 2.23/0.99      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 2.23/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK0)))) != iProver_top
% 2.23/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.23/0.99      | l1_pre_topc(X0_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(X0_51) != iProver_top ),
% 2.23/0.99      inference(renaming,[status(thm)],[c_3051]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3062,plain,
% 2.23/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK0,sK4,X0_51)
% 2.23/0.99      | m1_pre_topc(X0_51,sK3) != iProver_top
% 2.23/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 2.23/0.99      | v2_struct_0(sK3) = iProver_top
% 2.23/0.99      | l1_pre_topc(sK3) != iProver_top
% 2.23/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 2.23/0.99      inference(equality_resolution,[status(thm)],[c_3052]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_27,negated_conjecture,
% 2.23/0.99      ( v2_pre_topc(sK1) ),
% 2.23/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_36,plain,
% 2.23/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_26,negated_conjecture,
% 2.23/0.99      ( l1_pre_topc(sK1) ),
% 2.23/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_37,plain,
% 2.23/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_23,negated_conjecture,
% 2.23/0.99      ( ~ v2_struct_0(sK3) ),
% 2.23/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_40,plain,
% 2.23/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_41,plain,
% 2.23/0.99      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | v2_pre_topc(X0) ),
% 2.23/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_956,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.23/0.99      | ~ l1_pre_topc(X1_51)
% 2.23/0.99      | ~ v2_pre_topc(X1_51)
% 2.23/0.99      | v2_pre_topc(X0_51) ),
% 2.23/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1561,plain,
% 2.23/0.99      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 2.23/0.99      | l1_pre_topc(X1_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(X1_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(X0_51) = iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_956]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2049,plain,
% 2.23/0.99      ( l1_pre_topc(sK1) != iProver_top
% 2.23/0.99      | v2_pre_topc(sK3) = iProver_top
% 2.23/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 2.23/0.99      inference(superposition,[status(thm)],[c_1573,c_1561]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.23/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_955,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.23/0.99      | ~ l1_pre_topc(X1_51)
% 2.23/0.99      | l1_pre_topc(X0_51) ),
% 2.23/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2052,plain,
% 2.23/0.99      ( ~ m1_pre_topc(sK3,X0_51)
% 2.23/0.99      | ~ l1_pre_topc(X0_51)
% 2.23/0.99      | l1_pre_topc(sK3) ),
% 2.23/0.99      inference(instantiation,[status(thm)],[c_955]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2140,plain,
% 2.23/0.99      ( ~ m1_pre_topc(sK3,sK1) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK1) ),
% 2.23/0.99      inference(instantiation,[status(thm)],[c_2052]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2141,plain,
% 2.23/0.99      ( m1_pre_topc(sK3,sK1) != iProver_top
% 2.23/0.99      | l1_pre_topc(sK3) = iProver_top
% 2.23/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_2140]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3219,plain,
% 2.23/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK0,sK4,X0_51)
% 2.23/0.99      | m1_pre_topc(X0_51,sK3) != iProver_top ),
% 2.23/0.99      inference(global_propositional_subsumption,
% 2.23/0.99                [status(thm)],
% 2.23/0.99                [c_3062,c_36,c_37,c_40,c_41,c_44,c_2049,c_2141]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3227,plain,
% 2.23/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK0,sK4,sK2) ),
% 2.23/0.99      inference(superposition,[status(thm)],[c_1569,c_3219]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3322,plain,
% 2.23/0.99      ( k3_tmap_1(X0_51,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2)
% 2.23/0.99      | m1_pre_topc(sK3,X0_51) != iProver_top
% 2.23/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.23/0.99      | l1_pre_topc(X0_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(X0_51) != iProver_top ),
% 2.23/0.99      inference(light_normalisation,[status(thm)],[c_3321,c_3227]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3332,plain,
% 2.23/0.99      ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2)
% 2.23/0.99      | v2_struct_0(sK1) = iProver_top
% 2.23/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.23/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 2.23/0.99      inference(superposition,[status(thm)],[c_1573,c_3322]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_28,negated_conjecture,
% 2.23/0.99      ( ~ v2_struct_0(sK1) ),
% 2.23/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_35,plain,
% 2.23/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3370,plain,
% 2.23/0.99      ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2) ),
% 2.23/0.99      inference(global_propositional_subsumption,
% 2.23/0.99                [status(thm)],
% 2.23/0.99                [c_3332,c_35,c_36,c_37]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_11,negated_conjecture,
% 2.23/0.99      ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
% 2.23/0.99      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 2.23/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_952,negated_conjecture,
% 2.23/0.99      ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
% 2.23/0.99      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 2.23/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1565,plain,
% 2.23/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK5) != iProver_top
% 2.23/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_952]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_13,negated_conjecture,
% 2.23/0.99      ( sK5 = sK6 ),
% 2.23/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_950,negated_conjecture,
% 2.23/0.99      ( sK5 = sK6 ),
% 2.23/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1638,plain,
% 2.23/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 2.23/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
% 2.23/0.99      inference(light_normalisation,[status(thm)],[c_1565,c_950]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3374,plain,
% 2.23/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 2.23/0.99      | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) != iProver_top ),
% 2.23/0.99      inference(demodulation,[status(thm)],[c_3370,c_1638]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_12,negated_conjecture,
% 2.23/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK5)
% 2.23/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 2.23/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_951,negated_conjecture,
% 2.23/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK5)
% 2.23/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 2.23/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1566,plain,
% 2.23/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK5) = iProver_top
% 2.23/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_951]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1627,plain,
% 2.23/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 2.23/0.99      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
% 2.23/0.99      inference(light_normalisation,[status(thm)],[c_1566,c_950]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3373,plain,
% 2.23/0.99      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 2.23/0.99      | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) = iProver_top ),
% 2.23/0.99      inference(demodulation,[status(thm)],[c_3370,c_1627]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_9,plain,
% 2.23/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.23/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.23/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.23/0.99      | ~ v1_tsep_1(X4,X0)
% 2.23/0.99      | ~ m1_pre_topc(X4,X0)
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X0)
% 2.23/0.99      | v2_struct_0(X4)
% 2.23/0.99      | ~ v1_funct_1(X2)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ l1_pre_topc(X0)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X0) ),
% 2.23/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_463,plain,
% 2.23/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.23/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.23/0.99      | ~ v1_tsep_1(X4,X0)
% 2.23/0.99      | ~ m1_pre_topc(X4,X0)
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.23/0.99      | v2_struct_0(X0)
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X4)
% 2.23/0.99      | ~ v1_funct_1(X2)
% 2.23/0.99      | ~ l1_pre_topc(X0)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X0)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.23/0.99      | sK4 != X2 ),
% 2.23/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_464,plain,
% 2.23/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.23/0.99      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.23/0.99      | ~ v1_tsep_1(X0,X2)
% 2.23/0.99      | ~ m1_pre_topc(X0,X2)
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X0)
% 2.23/0.99      | ~ v1_funct_1(sK4)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(unflattening,[status(thm)],[c_463]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_468,plain,
% 2.23/0.99      ( v2_struct_0(X0)
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/0.99      | ~ m1_pre_topc(X0,X2)
% 2.23/0.99      | ~ v1_tsep_1(X0,X2)
% 2.23/0.99      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.23/0.99      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(global_propositional_subsumption,
% 2.23/0.99                [status(thm)],
% 2.23/0.99                [c_464,c_21]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_469,plain,
% 2.23/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.23/0.99      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 2.23/0.99      | ~ v1_tsep_1(X0,X2)
% 2.23/0.99      | ~ m1_pre_topc(X0,X2)
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.23/0.99      | v2_struct_0(X0)
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(renaming,[status(thm)],[c_468]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_932,plain,
% 2.23/0.99      ( r1_tmap_1(X0_51,X1_51,k2_tmap_1(X2_51,X1_51,sK4,X0_51),X0_52)
% 2.23/0.99      | ~ r1_tmap_1(X2_51,X1_51,sK4,X0_52)
% 2.23/0.99      | ~ v1_tsep_1(X0_51,X2_51)
% 2.23/0.99      | ~ m1_pre_topc(X0_51,X2_51)
% 2.23/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 2.23/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X2_51))
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
% 2.23/0.99      | v2_struct_0(X1_51)
% 2.23/0.99      | v2_struct_0(X2_51)
% 2.23/0.99      | v2_struct_0(X0_51)
% 2.23/0.99      | ~ l1_pre_topc(X1_51)
% 2.23/0.99      | ~ l1_pre_topc(X2_51)
% 2.23/0.99      | ~ v2_pre_topc(X1_51)
% 2.23/0.99      | ~ v2_pre_topc(X2_51)
% 2.23/0.99      | u1_struct_0(X2_51) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(subtyping,[status(esa)],[c_469]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2110,plain,
% 2.23/0.99      ( r1_tmap_1(X0_51,X1_51,k2_tmap_1(sK3,X1_51,sK4,X0_51),X0_52)
% 2.23/0.99      | ~ r1_tmap_1(sK3,X1_51,sK4,X0_52)
% 2.23/0.99      | ~ v1_tsep_1(X0_51,sK3)
% 2.23/0.99      | ~ m1_pre_topc(X0_51,sK3)
% 2.23/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 2.23/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_51))))
% 2.23/0.99      | v2_struct_0(X1_51)
% 2.23/0.99      | v2_struct_0(X0_51)
% 2.23/0.99      | v2_struct_0(sK3)
% 2.23/0.99      | ~ l1_pre_topc(X1_51)
% 2.23/0.99      | ~ l1_pre_topc(sK3)
% 2.23/0.99      | ~ v2_pre_topc(X1_51)
% 2.23/0.99      | ~ v2_pre_topc(sK3)
% 2.23/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK0)
% 2.23/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.23/0.99      inference(instantiation,[status(thm)],[c_932]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2273,plain,
% 2.23/0.99      ( ~ r1_tmap_1(sK3,X0_51,sK4,X0_52)
% 2.23/0.99      | r1_tmap_1(sK2,X0_51,k2_tmap_1(sK3,X0_51,sK4,sK2),X0_52)
% 2.23/0.99      | ~ v1_tsep_1(sK2,sK3)
% 2.23/0.99      | ~ m1_pre_topc(sK2,sK3)
% 2.23/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.23/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 2.23/0.99      | v2_struct_0(X0_51)
% 2.23/0.99      | v2_struct_0(sK3)
% 2.23/0.99      | v2_struct_0(sK2)
% 2.23/0.99      | ~ l1_pre_topc(X0_51)
% 2.23/0.99      | ~ l1_pre_topc(sK3)
% 2.23/0.99      | ~ v2_pre_topc(X0_51)
% 2.23/0.99      | ~ v2_pre_topc(sK3)
% 2.23/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.23/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.23/0.99      inference(instantiation,[status(thm)],[c_2110]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3110,plain,
% 2.23/0.99      ( ~ r1_tmap_1(sK3,X0_51,sK4,sK6)
% 2.23/0.99      | r1_tmap_1(sK2,X0_51,k2_tmap_1(sK3,X0_51,sK4,sK2),sK6)
% 2.23/0.99      | ~ v1_tsep_1(sK2,sK3)
% 2.23/0.99      | ~ m1_pre_topc(sK2,sK3)
% 2.23/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.23/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 2.23/0.99      | v2_struct_0(X0_51)
% 2.23/0.99      | v2_struct_0(sK3)
% 2.23/0.99      | v2_struct_0(sK2)
% 2.23/0.99      | ~ l1_pre_topc(X0_51)
% 2.23/0.99      | ~ l1_pre_topc(sK3)
% 2.23/0.99      | ~ v2_pre_topc(X0_51)
% 2.23/0.99      | ~ v2_pre_topc(sK3)
% 2.23/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.23/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.23/0.99      inference(instantiation,[status(thm)],[c_2273]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3111,plain,
% 2.23/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.23/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.23/0.99      | r1_tmap_1(sK3,X0_51,sK4,sK6) != iProver_top
% 2.23/0.99      | r1_tmap_1(sK2,X0_51,k2_tmap_1(sK3,X0_51,sK4,sK2),sK6) = iProver_top
% 2.23/0.99      | v1_tsep_1(sK2,sK3) != iProver_top
% 2.23/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.23/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.23/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 2.23/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51)))) != iProver_top
% 2.23/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.23/0.99      | v2_struct_0(sK3) = iProver_top
% 2.23/0.99      | v2_struct_0(sK2) = iProver_top
% 2.23/0.99      | l1_pre_topc(X0_51) != iProver_top
% 2.23/0.99      | l1_pre_topc(sK3) != iProver_top
% 2.23/0.99      | v2_pre_topc(X0_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_3110]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_3113,plain,
% 2.23/0.99      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 2.23/0.99      | r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 2.23/0.99      | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) = iProver_top
% 2.23/0.99      | v1_tsep_1(sK2,sK3) != iProver_top
% 2.23/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.23/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.23/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 2.23/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 2.23/0.99      | v2_struct_0(sK3) = iProver_top
% 2.23/0.99      | v2_struct_0(sK0) = iProver_top
% 2.23/0.99      | v2_struct_0(sK2) = iProver_top
% 2.23/0.99      | l1_pre_topc(sK3) != iProver_top
% 2.23/0.99      | l1_pre_topc(sK0) != iProver_top
% 2.23/0.99      | v2_pre_topc(sK3) != iProver_top
% 2.23/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 2.23/0.99      inference(instantiation,[status(thm)],[c_3111]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_8,plain,
% 2.23/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.23/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.23/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.23/0.99      | ~ v1_tsep_1(X4,X0)
% 2.23/0.99      | ~ m1_pre_topc(X4,X0)
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X0)
% 2.23/0.99      | v2_struct_0(X4)
% 2.23/0.99      | ~ v1_funct_1(X2)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ l1_pre_topc(X0)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X0) ),
% 2.23/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_523,plain,
% 2.23/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.23/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.23/0.99      | ~ v1_tsep_1(X4,X0)
% 2.23/0.99      | ~ m1_pre_topc(X4,X0)
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.23/0.99      | v2_struct_0(X0)
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X4)
% 2.23/0.99      | ~ v1_funct_1(X2)
% 2.23/0.99      | ~ l1_pre_topc(X0)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X0)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.23/0.99      | sK4 != X2 ),
% 2.23/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_524,plain,
% 2.23/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.23/0.99      | r1_tmap_1(X2,X1,sK4,X3)
% 2.23/0.99      | ~ v1_tsep_1(X0,X2)
% 2.23/0.99      | ~ m1_pre_topc(X0,X2)
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X0)
% 2.23/0.99      | ~ v1_funct_1(sK4)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(unflattening,[status(thm)],[c_523]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_528,plain,
% 2.23/0.99      ( v2_struct_0(X0)
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/0.99      | ~ m1_pre_topc(X0,X2)
% 2.23/0.99      | ~ v1_tsep_1(X0,X2)
% 2.23/0.99      | r1_tmap_1(X2,X1,sK4,X3)
% 2.23/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(global_propositional_subsumption,
% 2.23/0.99                [status(thm)],
% 2.23/0.99                [c_524,c_21]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_529,plain,
% 2.23/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 2.23/0.99      | r1_tmap_1(X2,X1,sK4,X3)
% 2.23/0.99      | ~ v1_tsep_1(X0,X2)
% 2.23/0.99      | ~ m1_pre_topc(X0,X2)
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.23/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.23/0.99      | v2_struct_0(X0)
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ l1_pre_topc(X2)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X2)
% 2.23/0.99      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(renaming,[status(thm)],[c_528]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_931,plain,
% 2.23/0.99      ( ~ r1_tmap_1(X0_51,X1_51,k2_tmap_1(X2_51,X1_51,sK4,X0_51),X0_52)
% 2.23/0.99      | r1_tmap_1(X2_51,X1_51,sK4,X0_52)
% 2.23/0.99      | ~ v1_tsep_1(X0_51,X2_51)
% 2.23/0.99      | ~ m1_pre_topc(X0_51,X2_51)
% 2.23/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 2.23/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X2_51))
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
% 2.23/0.99      | v2_struct_0(X1_51)
% 2.23/0.99      | v2_struct_0(X2_51)
% 2.23/0.99      | v2_struct_0(X0_51)
% 2.23/0.99      | ~ l1_pre_topc(X1_51)
% 2.23/0.99      | ~ l1_pre_topc(X2_51)
% 2.23/0.99      | ~ v2_pre_topc(X1_51)
% 2.23/0.99      | ~ v2_pre_topc(X2_51)
% 2.23/0.99      | u1_struct_0(X2_51) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK0) ),
% 2.23/0.99      inference(subtyping,[status(esa)],[c_529]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2111,plain,
% 2.23/0.99      ( ~ r1_tmap_1(X0_51,X1_51,k2_tmap_1(sK3,X1_51,sK4,X0_51),X0_52)
% 2.23/0.99      | r1_tmap_1(sK3,X1_51,sK4,X0_52)
% 2.23/0.99      | ~ v1_tsep_1(X0_51,sK3)
% 2.23/0.99      | ~ m1_pre_topc(X0_51,sK3)
% 2.23/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 2.23/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1_51))))
% 2.23/0.99      | v2_struct_0(X1_51)
% 2.23/0.99      | v2_struct_0(X0_51)
% 2.23/0.99      | v2_struct_0(sK3)
% 2.23/0.99      | ~ l1_pre_topc(X1_51)
% 2.23/0.99      | ~ l1_pre_topc(sK3)
% 2.23/0.99      | ~ v2_pre_topc(X1_51)
% 2.23/0.99      | ~ v2_pre_topc(sK3)
% 2.23/0.99      | u1_struct_0(X1_51) != u1_struct_0(sK0)
% 2.23/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.23/0.99      inference(instantiation,[status(thm)],[c_931]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2278,plain,
% 2.23/0.99      ( r1_tmap_1(sK3,X0_51,sK4,X0_52)
% 2.23/0.99      | ~ r1_tmap_1(sK2,X0_51,k2_tmap_1(sK3,X0_51,sK4,sK2),X0_52)
% 2.23/0.99      | ~ v1_tsep_1(sK2,sK3)
% 2.23/0.99      | ~ m1_pre_topc(sK2,sK3)
% 2.23/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.23/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK2))
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 2.23/0.99      | v2_struct_0(X0_51)
% 2.23/0.99      | v2_struct_0(sK3)
% 2.23/0.99      | v2_struct_0(sK2)
% 2.23/0.99      | ~ l1_pre_topc(X0_51)
% 2.23/0.99      | ~ l1_pre_topc(sK3)
% 2.23/0.99      | ~ v2_pre_topc(X0_51)
% 2.23/0.99      | ~ v2_pre_topc(sK3)
% 2.23/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.23/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.23/0.99      inference(instantiation,[status(thm)],[c_2111]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2992,plain,
% 2.23/0.99      ( r1_tmap_1(sK3,X0_51,sK4,sK6)
% 2.23/0.99      | ~ r1_tmap_1(sK2,X0_51,k2_tmap_1(sK3,X0_51,sK4,sK2),sK6)
% 2.23/0.99      | ~ v1_tsep_1(sK2,sK3)
% 2.23/0.99      | ~ m1_pre_topc(sK2,sK3)
% 2.23/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 2.23/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.23/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51))))
% 2.23/0.99      | v2_struct_0(X0_51)
% 2.23/0.99      | v2_struct_0(sK3)
% 2.23/0.99      | v2_struct_0(sK2)
% 2.23/0.99      | ~ l1_pre_topc(X0_51)
% 2.23/0.99      | ~ l1_pre_topc(sK3)
% 2.23/0.99      | ~ v2_pre_topc(X0_51)
% 2.23/0.99      | ~ v2_pre_topc(sK3)
% 2.23/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.23/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.23/0.99      inference(instantiation,[status(thm)],[c_2278]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2993,plain,
% 2.23/0.99      ( u1_struct_0(X0_51) != u1_struct_0(sK0)
% 2.23/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.23/0.99      | r1_tmap_1(sK3,X0_51,sK4,sK6) = iProver_top
% 2.23/0.99      | r1_tmap_1(sK2,X0_51,k2_tmap_1(sK3,X0_51,sK4,sK2),sK6) != iProver_top
% 2.23/0.99      | v1_tsep_1(sK2,sK3) != iProver_top
% 2.23/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.23/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.23/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 2.23/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_51)))) != iProver_top
% 2.23/0.99      | v2_struct_0(X0_51) = iProver_top
% 2.23/0.99      | v2_struct_0(sK3) = iProver_top
% 2.23/0.99      | v2_struct_0(sK2) = iProver_top
% 2.23/0.99      | l1_pre_topc(X0_51) != iProver_top
% 2.23/0.99      | l1_pre_topc(sK3) != iProver_top
% 2.23/0.99      | v2_pre_topc(X0_51) != iProver_top
% 2.23/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_2992]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2995,plain,
% 2.23/0.99      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.23/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 2.23/0.99      | r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 2.23/0.99      | r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) != iProver_top
% 2.23/0.99      | v1_tsep_1(sK2,sK3) != iProver_top
% 2.23/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.23/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.23/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 2.23/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 2.23/0.99      | v2_struct_0(sK3) = iProver_top
% 2.23/0.99      | v2_struct_0(sK0) = iProver_top
% 2.23/0.99      | v2_struct_0(sK2) = iProver_top
% 2.23/0.99      | l1_pre_topc(sK3) != iProver_top
% 2.23/0.99      | l1_pre_topc(sK0) != iProver_top
% 2.23/0.99      | v2_pre_topc(sK3) != iProver_top
% 2.23/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 2.23/0.99      inference(instantiation,[status(thm)],[c_2993]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_958,plain,( X0_52 = X0_52 ),theory(equality) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2618,plain,
% 2.23/0.99      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 2.23/0.99      inference(instantiation,[status(thm)],[c_958]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_0,plain,
% 2.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.23/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_6,plain,
% 2.23/0.99      ( ~ v1_tsep_1(X0,X1)
% 2.23/0.99      | v1_tsep_1(X0,X2)
% 2.23/0.99      | ~ m1_pre_topc(X0,X1)
% 2.23/0.99      | ~ m1_pre_topc(X2,X1)
% 2.23/0.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X1) ),
% 2.23/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_381,plain,
% 2.23/0.99      ( ~ v1_tsep_1(X0,X1)
% 2.23/0.99      | v1_tsep_1(X0,X2)
% 2.23/0.99      | ~ m1_pre_topc(X2,X1)
% 2.23/0.99      | ~ m1_pre_topc(X0,X1)
% 2.23/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X1)
% 2.23/0.99      | u1_struct_0(X2) != X4
% 2.23/0.99      | u1_struct_0(X0) != X3 ),
% 2.23/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_382,plain,
% 2.23/0.99      ( ~ v1_tsep_1(X0,X1)
% 2.23/0.99      | v1_tsep_1(X0,X2)
% 2.23/0.99      | ~ m1_pre_topc(X0,X1)
% 2.23/0.99      | ~ m1_pre_topc(X2,X1)
% 2.23/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2)))
% 2.23/0.99      | v2_struct_0(X1)
% 2.23/0.99      | v2_struct_0(X2)
% 2.23/0.99      | ~ l1_pre_topc(X1)
% 2.23/0.99      | ~ v2_pre_topc(X1) ),
% 2.23/0.99      inference(unflattening,[status(thm)],[c_381]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_934,plain,
% 2.23/0.99      ( ~ v1_tsep_1(X0_51,X1_51)
% 2.23/0.99      | v1_tsep_1(X0_51,X2_51)
% 2.23/0.99      | ~ m1_pre_topc(X0_51,X1_51)
% 2.23/0.99      | ~ m1_pre_topc(X2_51,X1_51)
% 2.23/0.99      | ~ m1_subset_1(u1_struct_0(X0_51),k1_zfmisc_1(u1_struct_0(X2_51)))
% 2.23/0.99      | v2_struct_0(X1_51)
% 2.23/0.99      | v2_struct_0(X2_51)
% 2.23/0.99      | ~ l1_pre_topc(X1_51)
% 2.23/0.99      | ~ v2_pre_topc(X1_51) ),
% 2.23/0.99      inference(subtyping,[status(esa)],[c_382]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1938,plain,
% 2.23/0.99      ( v1_tsep_1(sK2,X0_51)
% 2.23/0.99      | ~ v1_tsep_1(sK2,sK1)
% 2.23/0.99      | ~ m1_pre_topc(X0_51,sK1)
% 2.23/0.99      | ~ m1_pre_topc(sK2,sK1)
% 2.23/0.99      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0_51)))
% 2.23/0.99      | v2_struct_0(X0_51)
% 2.23/0.99      | v2_struct_0(sK1)
% 2.23/0.99      | ~ l1_pre_topc(sK1)
% 2.23/0.99      | ~ v2_pre_topc(sK1) ),
% 2.23/0.99      inference(instantiation,[status(thm)],[c_934]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2060,plain,
% 2.23/0.99      ( v1_tsep_1(sK2,sK3)
% 2.23/0.99      | ~ v1_tsep_1(sK2,sK1)
% 2.23/0.99      | ~ m1_pre_topc(sK3,sK1)
% 2.23/0.99      | ~ m1_pre_topc(sK2,sK1)
% 2.23/0.99      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.23/0.99      | v2_struct_0(sK3)
% 2.23/0.99      | v2_struct_0(sK1)
% 2.23/0.99      | ~ l1_pre_topc(sK1)
% 2.23/0.99      | ~ v2_pre_topc(sK1) ),
% 2.23/0.99      inference(instantiation,[status(thm)],[c_1938]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_2061,plain,
% 2.23/0.99      ( v1_tsep_1(sK2,sK3) = iProver_top
% 2.23/0.99      | v1_tsep_1(sK2,sK1) != iProver_top
% 2.23/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.23/0.99      | m1_pre_topc(sK2,sK1) != iProver_top
% 2.23/0.99      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.23/0.99      | v2_struct_0(sK3) = iProver_top
% 2.23/0.99      | v2_struct_0(sK1) = iProver_top
% 2.23/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.23/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_2060]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_7,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.23/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.23/0.99      | ~ l1_pre_topc(X1) ),
% 2.23/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_954,plain,
% 2.23/0.99      ( ~ m1_pre_topc(X0_51,X1_51)
% 2.23/0.99      | m1_subset_1(u1_struct_0(X0_51),k1_zfmisc_1(u1_struct_0(X1_51)))
% 2.23/0.99      | ~ l1_pre_topc(X1_51) ),
% 2.23/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1900,plain,
% 2.23/0.99      ( ~ m1_pre_topc(sK2,sK3)
% 2.23/0.99      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.23/0.99      | ~ l1_pre_topc(sK3) ),
% 2.23/0.99      inference(instantiation,[status(thm)],[c_954]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1901,plain,
% 2.23/0.99      ( m1_pre_topc(sK2,sK3) != iProver_top
% 2.23/0.99      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.23/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_1900]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1870,plain,
% 2.23/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 2.23/0.99      inference(instantiation,[status(thm)],[c_958]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_15,negated_conjecture,
% 2.23/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 2.23/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_948,negated_conjecture,
% 2.23/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 2.23/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1568,plain,
% 2.23/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_1616,plain,
% 2.23/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.23/0.99      inference(light_normalisation,[status(thm)],[c_1568,c_950]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_14,negated_conjecture,
% 2.23/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 2.23/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_49,plain,
% 2.23/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_47,plain,
% 2.23/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_18,negated_conjecture,
% 2.23/0.99      ( v1_tsep_1(sK2,sK1) ),
% 2.23/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_45,plain,
% 2.23/0.99      ( v1_tsep_1(sK2,sK1) = iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_24,negated_conjecture,
% 2.23/0.99      ( m1_pre_topc(sK2,sK1) ),
% 2.23/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_39,plain,
% 2.23/0.99      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_25,negated_conjecture,
% 2.23/0.99      ( ~ v2_struct_0(sK2) ),
% 2.23/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(c_38,plain,
% 2.23/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 2.23/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.23/0.99  
% 2.23/0.99  cnf(contradiction,plain,
% 2.23/0.99      ( $false ),
% 2.23/0.99      inference(minisat,
% 2.23/0.99                [status(thm)],
% 2.23/0.99                [c_3374,c_3373,c_3113,c_2995,c_2618,c_2141,c_2061,c_2049,
% 2.23/0.99                 c_1901,c_1870,c_1616,c_49,c_47,c_45,c_44,c_41,c_40,c_39,
% 2.23/0.99                 c_38,c_37,c_36,c_35,c_34,c_33,c_32]) ).
% 2.23/0.99  
% 2.23/0.99  
% 2.23/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.23/0.99  
% 2.23/0.99  ------                               Statistics
% 2.23/0.99  
% 2.23/0.99  ------ General
% 2.23/0.99  
% 2.23/0.99  abstr_ref_over_cycles:                  0
% 2.23/0.99  abstr_ref_under_cycles:                 0
% 2.23/0.99  gc_basic_clause_elim:                   0
% 2.23/0.99  forced_gc_time:                         0
% 2.23/0.99  parsing_time:                           0.01
% 2.23/0.99  unif_index_cands_time:                  0.
% 2.23/0.99  unif_index_add_time:                    0.
% 2.23/0.99  orderings_time:                         0.
% 2.23/0.99  out_proof_time:                         0.014
% 2.23/0.99  total_time:                             0.147
% 2.23/0.99  num_of_symbols:                         56
% 2.23/0.99  num_of_terms:                           2108
% 2.23/0.99  
% 2.23/0.99  ------ Preprocessing
% 2.23/0.99  
% 2.23/0.99  num_of_splits:                          0
% 2.23/0.99  num_of_split_atoms:                     0
% 2.23/0.99  num_of_reused_defs:                     0
% 2.23/0.99  num_eq_ax_congr_red:                    25
% 2.23/0.99  num_of_sem_filtered_clauses:            1
% 2.23/0.99  num_of_subtypes:                        2
% 2.23/0.99  monotx_restored_types:                  0
% 2.23/0.99  sat_num_of_epr_types:                   0
% 2.23/0.99  sat_num_of_non_cyclic_types:            0
% 2.23/0.99  sat_guarded_non_collapsed_types:        0
% 2.23/0.99  num_pure_diseq_elim:                    0
% 2.23/0.99  simp_replaced_by:                       0
% 2.23/0.99  res_preprocessed:                       134
% 2.23/0.99  prep_upred:                             0
% 2.23/0.99  prep_unflattend:                        8
% 2.23/0.99  smt_new_axioms:                         0
% 2.23/0.99  pred_elim_cands:                        7
% 2.23/0.99  pred_elim:                              3
% 2.23/0.99  pred_elim_cl:                           3
% 2.23/0.99  pred_elim_cycles:                       5
% 2.23/0.99  merged_defs:                            8
% 2.23/0.99  merged_defs_ncl:                        0
% 2.23/0.99  bin_hyper_res:                          8
% 2.23/0.99  prep_cycles:                            4
% 2.23/0.99  pred_elim_time:                         0.011
% 2.23/0.99  splitting_time:                         0.
% 2.23/0.99  sem_filter_time:                        0.
% 2.23/0.99  monotx_time:                            0.
% 2.23/0.99  subtype_inf_time:                       0.
% 2.23/0.99  
% 2.23/0.99  ------ Problem properties
% 2.23/0.99  
% 2.23/0.99  clauses:                                28
% 2.23/0.99  conjectures:                            18
% 2.23/0.99  epr:                                    16
% 2.23/0.99  horn:                                   21
% 2.23/0.99  ground:                                 18
% 2.23/0.99  unary:                                  16
% 2.23/0.99  binary:                                 2
% 2.23/0.99  lits:                                   108
% 2.23/0.99  lits_eq:                                11
% 2.23/0.99  fd_pure:                                0
% 2.23/0.99  fd_pseudo:                              0
% 2.23/0.99  fd_cond:                                0
% 2.23/0.99  fd_pseudo_cond:                         0
% 2.23/0.99  ac_symbols:                             0
% 2.23/0.99  
% 2.23/0.99  ------ Propositional Solver
% 2.23/0.99  
% 2.23/0.99  prop_solver_calls:                      28
% 2.23/0.99  prop_fast_solver_calls:                 1437
% 2.23/0.99  smt_solver_calls:                       0
% 2.23/0.99  smt_fast_solver_calls:                  0
% 2.23/0.99  prop_num_of_clauses:                    754
% 2.23/0.99  prop_preprocess_simplified:             3641
% 2.23/0.99  prop_fo_subsumed:                       53
% 2.23/0.99  prop_solver_time:                       0.
% 2.23/0.99  smt_solver_time:                        0.
% 2.23/0.99  smt_fast_solver_time:                   0.
% 2.23/0.99  prop_fast_solver_time:                  0.
% 2.23/0.99  prop_unsat_core_time:                   0.
% 2.23/0.99  
% 2.23/0.99  ------ QBF
% 2.23/0.99  
% 2.23/0.99  qbf_q_res:                              0
% 2.23/0.99  qbf_num_tautologies:                    0
% 2.23/0.99  qbf_prep_cycles:                        0
% 2.23/0.99  
% 2.23/0.99  ------ BMC1
% 2.23/0.99  
% 2.23/0.99  bmc1_current_bound:                     -1
% 2.23/0.99  bmc1_last_solved_bound:                 -1
% 2.23/0.99  bmc1_unsat_core_size:                   -1
% 2.23/0.99  bmc1_unsat_core_parents_size:           -1
% 2.23/0.99  bmc1_merge_next_fun:                    0
% 2.23/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.23/0.99  
% 2.23/0.99  ------ Instantiation
% 2.23/0.99  
% 2.23/0.99  inst_num_of_clauses:                    238
% 2.23/0.99  inst_num_in_passive:                    12
% 2.23/0.99  inst_num_in_active:                     212
% 2.23/0.99  inst_num_in_unprocessed:                14
% 2.23/0.99  inst_num_of_loops:                      250
% 2.23/0.99  inst_num_of_learning_restarts:          0
% 2.23/0.99  inst_num_moves_active_passive:          33
% 2.23/0.99  inst_lit_activity:                      0
% 2.23/0.99  inst_lit_activity_moves:                0
% 2.23/0.99  inst_num_tautologies:                   0
% 2.23/0.99  inst_num_prop_implied:                  0
% 2.23/0.99  inst_num_existing_simplified:           0
% 2.23/0.99  inst_num_eq_res_simplified:             0
% 2.23/0.99  inst_num_child_elim:                    0
% 2.23/0.99  inst_num_of_dismatching_blockings:      18
% 2.23/0.99  inst_num_of_non_proper_insts:           272
% 2.23/0.99  inst_num_of_duplicates:                 0
% 2.23/0.99  inst_inst_num_from_inst_to_res:         0
% 2.23/0.99  inst_dismatching_checking_time:         0.
% 2.23/0.99  
% 2.23/0.99  ------ Resolution
% 2.23/0.99  
% 2.23/0.99  res_num_of_clauses:                     0
% 2.23/0.99  res_num_in_passive:                     0
% 2.23/0.99  res_num_in_active:                      0
% 2.23/0.99  res_num_of_loops:                       138
% 2.23/0.99  res_forward_subset_subsumed:            60
% 2.23/0.99  res_backward_subset_subsumed:           0
% 2.23/0.99  res_forward_subsumed:                   0
% 2.23/0.99  res_backward_subsumed:                  0
% 2.23/0.99  res_forward_subsumption_resolution:     1
% 2.23/0.99  res_backward_subsumption_resolution:    0
% 2.23/0.99  res_clause_to_clause_subsumption:       192
% 2.23/0.99  res_orphan_elimination:                 0
% 2.23/0.99  res_tautology_del:                      94
% 2.23/0.99  res_num_eq_res_simplified:              0
% 2.23/0.99  res_num_sel_changes:                    0
% 2.23/0.99  res_moves_from_active_to_pass:          0
% 2.23/0.99  
% 2.23/0.99  ------ Superposition
% 2.23/0.99  
% 2.23/0.99  sup_time_total:                         0.
% 2.23/0.99  sup_time_generating:                    0.
% 2.23/0.99  sup_time_sim_full:                      0.
% 2.23/0.99  sup_time_sim_immed:                     0.
% 2.23/0.99  
% 2.23/0.99  sup_num_of_clauses:                     53
% 2.23/0.99  sup_num_in_active:                      47
% 2.23/0.99  sup_num_in_passive:                     6
% 2.23/0.99  sup_num_of_loops:                       49
% 2.23/0.99  sup_fw_superposition:                   18
% 2.23/0.99  sup_bw_superposition:                   2
% 2.23/0.99  sup_immediate_simplified:               1
% 2.23/0.99  sup_given_eliminated:                   0
% 2.23/0.99  comparisons_done:                       0
% 2.23/0.99  comparisons_avoided:                    0
% 2.23/0.99  
% 2.23/0.99  ------ Simplifications
% 2.23/0.99  
% 2.23/0.99  
% 2.23/0.99  sim_fw_subset_subsumed:                 0
% 2.23/0.99  sim_bw_subset_subsumed:                 0
% 2.23/0.99  sim_fw_subsumed:                        0
% 2.23/0.99  sim_bw_subsumed:                        0
% 2.23/0.99  sim_fw_subsumption_res:                 2
% 2.23/0.99  sim_bw_subsumption_res:                 0
% 2.23/0.99  sim_tautology_del:                      2
% 2.23/0.99  sim_eq_tautology_del:                   0
% 2.23/0.99  sim_eq_res_simp:                        0
% 2.23/0.99  sim_fw_demodulated:                     0
% 2.23/0.99  sim_bw_demodulated:                     2
% 2.23/0.99  sim_light_normalised:                   4
% 2.23/0.99  sim_joinable_taut:                      0
% 2.23/0.99  sim_joinable_simp:                      0
% 2.23/0.99  sim_ac_normalised:                      0
% 2.23/0.99  sim_smt_subsumption:                    0
% 2.23/0.99  
%------------------------------------------------------------------------------
