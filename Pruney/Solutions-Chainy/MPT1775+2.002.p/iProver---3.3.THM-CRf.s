%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:16 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 992 expanded)
%              Number of clauses        :  123 ( 189 expanded)
%              Number of leaves         :   23 ( 397 expanded)
%              Depth                    :   29
%              Number of atoms          : 1716 (17701 expanded)
%              Number of equality atoms :  350 (1345 expanded)
%              Maximal formula depth    :   32 (   9 average)
%              Maximal clause size      :   44 (   7 average)
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
    inference(negated_conjecture,[],[f14])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            | ~ r1_tmap_1(X3,X1,X4,X5) )
          & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            | r1_tmap_1(X3,X1,X4,X5) )
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
          | ~ r1_tmap_1(X3,X1,X4,X5) )
        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
          | r1_tmap_1(X3,X1,X4,X5) )
        & sK7 = X5
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
              | ~ r1_tmap_1(X3,X1,X4,sK6) )
            & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              | r1_tmap_1(X3,X1,X4,sK6) )
            & sK6 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6)
                  | ~ r1_tmap_1(X3,X1,sK5,X5) )
                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6)
                  | r1_tmap_1(X3,X1,sK5,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & v1_tsep_1(X2,X3)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6)
                      | ~ r1_tmap_1(sK4,X1,X4,X5) )
                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6)
                      | r1_tmap_1(sK4,X1,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK4)) )
            & m1_pre_topc(X2,sK4)
            & v1_tsep_1(X2,sK4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
                        ( ( ~ r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6)
                          | ~ r1_tmap_1(X3,X1,X4,X5) )
                        & ( r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6)
                          | r1_tmap_1(X3,X1,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK3)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK3,X3)
                & v1_tsep_1(sK3,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
                            ( ( ~ r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,sK2,X4,X5) )
                            & ( r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6)
                              | r1_tmap_1(X3,sK2,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & v1_tsep_1(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
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
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
      | ~ r1_tmap_1(sK4,sK2,sK5,sK6) )
    & ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
      | r1_tmap_1(sK4,sK2,sK5,sK6) )
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK3))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_pre_topc(sK3,sK4)
    & v1_tsep_1(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK1)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f47,f54,f53,f52,f51,f50,f49,f48])).

fof(f93,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f41])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f104,plain,(
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
    inference(equality_resolution,[],[f75])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f102,plain,(
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
    inference(equality_resolution,[],[f74])).

fof(f88,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,
    ( ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
    | ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f94,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f55])).

fof(f95,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
    | r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
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
    inference(equality_resolution,[],[f76])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f69])).

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

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,(
    v1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f79,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f77,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f78,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2311,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_10])).

cnf(c_235,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_234])).

cnf(c_11,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_531,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | X4 != X2
    | X3 != X0
    | sK0(X4,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_235,c_11])).

cnf(c_532,plain,
    ( r2_hidden(X0,sK0(X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_2297,plain,
    ( r2_hidden(X0,sK0(X1,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_552,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | X3 != X1
    | X2 != X0
    | sK0(X3,X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_11])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_2296,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2318,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3856,plain,
    ( r2_hidden(X0,sK0(X1,X2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2296,c_2318])).

cnf(c_5086,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2297,c_3856])).

cnf(c_5140,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2311,c_5086])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3534,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4291,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_3534])).

cnf(c_4292,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4291])).

cnf(c_20,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r2_hidden(X3,X6)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_18,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_211,plain,
    ( ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_18])).

cnf(c_212,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_211])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_664,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_212,c_29])).

cnf(c_665,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_669,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_665,c_30])).

cnf(c_670,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_669])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_711,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_670,c_17])).

cnf(c_2295,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) = iProver_top
    | r1_tmap_1(X0,X1,sK5,X4) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_3098,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2295])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_49,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1513,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2597,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1513])).

cnf(c_2598,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
    | ~ r1_tmap_1(sK4,X1,sK5,X3)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_2599,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2598])).

cnf(c_3592,plain,
    ( v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3098,c_49,c_2597,c_2599])).

cnf(c_3593,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3592])).

cnf(c_3613,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3593])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_44,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_45,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_46,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_53,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4042,plain,
    ( v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3613,c_44,c_45,c_46,c_53])).

cnf(c_4043,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4042])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK6)
    | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2313,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK6) != iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2411,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2313,c_23])).

cnf(c_4058,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4043,c_2411])).

cnf(c_3157,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3749,plain,
    ( ~ m1_pre_topc(sK4,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3157])).

cnf(c_3750,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3749])).

cnf(c_22,negated_conjecture,
    ( r1_tmap_1(sK4,sK2,sK5,sK6)
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2312,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK6) = iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2394,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2312,c_23])).

cnf(c_19,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r2_hidden(X3,X6)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_15,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_220,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_16])).

cnf(c_221,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_220])).

cnf(c_27,negated_conjecture,
    ( v1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_510,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_221,c_27])).

cnf(c_511,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK4)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_513,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_26])).

cnf(c_585,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ r2_hidden(X3,X6)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(sK3) != X6
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_513])).

cnf(c_586,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,X3),X4)
    | r1_tmap_1(sK4,X1,X3,X4)
    | ~ v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ r2_hidden(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_590,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r2_hidden(X4,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK4,X2)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(X0,X2)
    | ~ v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(X1))
    | r1_tmap_1(sK4,X1,X3,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,X3),X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_586,c_32])).

cnf(c_591,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,X3),X4)
    | r1_tmap_1(sK4,X1,X3,X4)
    | ~ v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ r2_hidden(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(sK4) ),
    inference(renaming,[status(thm)],[c_590])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_640,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,X3),X4)
    | r1_tmap_1(sK4,X1,X3,X4)
    | ~ v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ r2_hidden(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_591,c_8,c_9,c_17])).

cnf(c_788,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,X3),X4)
    | r1_tmap_1(sK4,X1,X3,X4)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ r2_hidden(X4,u1_struct_0(sK3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_640])).

cnf(c_789,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
    | r1_tmap_1(sK4,X1,sK5,X3)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ r2_hidden(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_788])).

cnf(c_793,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK4,X2)
    | ~ m1_pre_topc(X0,sK4)
    | r1_tmap_1(sK4,X1,sK5,X3)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_789,c_30])).

cnf(c_794,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
    | r1_tmap_1(sK4,X1,sK5,X3)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ r2_hidden(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_793])).

cnf(c_2294,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | r2_hidden(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_2759,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | r2_hidden(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2294])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_43,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_50,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_55,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2622,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2623,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2622])).

cnf(c_2765,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3019,plain,
    ( ~ m1_pre_topc(sK4,sK1)
    | l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2765])).

cnf(c_3020,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3019])).

cnf(c_3103,plain,
    ( v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2759,c_43,c_44,c_45,c_46,c_50,c_53,c_55,c_2623,c_3020])).

cnf(c_3104,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | r2_hidden(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3103])).

cnf(c_3121,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | r2_hidden(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2394,c_3104])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_41,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_42,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_47,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_57,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2310,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2351,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2310,c_23])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3559,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3560,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3559])).

cnf(c_3585,plain,
    ( r2_hidden(sK7,u1_struct_0(sK3)) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3121,c_41,c_42,c_43,c_47,c_50,c_55,c_57,c_2351,c_3560])).

cnf(c_3586,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
    | r2_hidden(sK7,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3585])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2319,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3256,plain,
    ( r2_hidden(sK7,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2311,c_2319])).

cnf(c_2309,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2316,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3234,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2309,c_2316])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5140,c_4292,c_4058,c_3750,c_3586,c_3256,c_3234,c_3020,c_2351,c_57,c_55,c_50,c_47,c_43,c_42,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n006.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 17:33:07 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 2.69/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/0.98  
% 2.69/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/0.98  
% 2.69/0.98  ------  iProver source info
% 2.69/0.98  
% 2.69/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.69/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/0.98  git: non_committed_changes: false
% 2.69/0.98  git: last_make_outside_of_git: false
% 2.69/0.98  
% 2.69/0.98  ------ 
% 2.69/0.98  
% 2.69/0.98  ------ Input Options
% 2.69/0.98  
% 2.69/0.98  --out_options                           all
% 2.69/0.98  --tptp_safe_out                         true
% 2.69/0.98  --problem_path                          ""
% 2.69/0.98  --include_path                          ""
% 2.69/0.98  --clausifier                            res/vclausify_rel
% 2.69/0.98  --clausifier_options                    --mode clausify
% 2.69/0.98  --stdin                                 false
% 2.69/0.98  --stats_out                             all
% 2.69/0.98  
% 2.69/0.98  ------ General Options
% 2.69/0.98  
% 2.69/0.98  --fof                                   false
% 2.69/0.98  --time_out_real                         305.
% 2.69/0.98  --time_out_virtual                      -1.
% 2.69/0.98  --symbol_type_check                     false
% 2.69/0.98  --clausify_out                          false
% 2.69/0.98  --sig_cnt_out                           false
% 2.69/0.98  --trig_cnt_out                          false
% 2.69/0.98  --trig_cnt_out_tolerance                1.
% 2.69/0.98  --trig_cnt_out_sk_spl                   false
% 2.69/0.98  --abstr_cl_out                          false
% 2.69/0.98  
% 2.69/0.98  ------ Global Options
% 2.69/0.98  
% 2.69/0.98  --schedule                              default
% 2.69/0.98  --add_important_lit                     false
% 2.69/0.98  --prop_solver_per_cl                    1000
% 2.69/0.98  --min_unsat_core                        false
% 2.69/0.98  --soft_assumptions                      false
% 2.69/0.98  --soft_lemma_size                       3
% 2.69/0.98  --prop_impl_unit_size                   0
% 2.69/0.98  --prop_impl_unit                        []
% 2.69/0.98  --share_sel_clauses                     true
% 2.69/0.98  --reset_solvers                         false
% 2.69/0.98  --bc_imp_inh                            [conj_cone]
% 2.69/0.98  --conj_cone_tolerance                   3.
% 2.69/0.98  --extra_neg_conj                        none
% 2.69/0.98  --large_theory_mode                     true
% 2.69/0.98  --prolific_symb_bound                   200
% 2.69/0.98  --lt_threshold                          2000
% 2.69/0.98  --clause_weak_htbl                      true
% 2.69/0.98  --gc_record_bc_elim                     false
% 2.69/0.98  
% 2.69/0.98  ------ Preprocessing Options
% 2.69/0.98  
% 2.69/0.98  --preprocessing_flag                    true
% 2.69/0.98  --time_out_prep_mult                    0.1
% 2.69/0.98  --splitting_mode                        input
% 2.69/0.98  --splitting_grd                         true
% 2.69/0.98  --splitting_cvd                         false
% 2.69/0.98  --splitting_cvd_svl                     false
% 2.69/0.98  --splitting_nvd                         32
% 2.69/0.98  --sub_typing                            true
% 2.69/0.98  --prep_gs_sim                           true
% 2.69/0.98  --prep_unflatten                        true
% 2.69/0.98  --prep_res_sim                          true
% 2.69/0.98  --prep_upred                            true
% 2.69/0.98  --prep_sem_filter                       exhaustive
% 2.69/0.98  --prep_sem_filter_out                   false
% 2.69/0.98  --pred_elim                             true
% 2.69/0.98  --res_sim_input                         true
% 2.69/0.98  --eq_ax_congr_red                       true
% 2.69/0.98  --pure_diseq_elim                       true
% 2.69/0.98  --brand_transform                       false
% 2.69/0.98  --non_eq_to_eq                          false
% 2.69/0.98  --prep_def_merge                        true
% 2.69/0.98  --prep_def_merge_prop_impl              false
% 2.69/0.98  --prep_def_merge_mbd                    true
% 2.69/0.98  --prep_def_merge_tr_red                 false
% 2.69/0.98  --prep_def_merge_tr_cl                  false
% 2.69/0.98  --smt_preprocessing                     true
% 2.69/0.98  --smt_ac_axioms                         fast
% 2.69/0.98  --preprocessed_out                      false
% 2.69/0.98  --preprocessed_stats                    false
% 2.69/0.98  
% 2.69/0.98  ------ Abstraction refinement Options
% 2.69/0.98  
% 2.69/0.98  --abstr_ref                             []
% 2.69/0.98  --abstr_ref_prep                        false
% 2.69/0.98  --abstr_ref_until_sat                   false
% 2.69/0.98  --abstr_ref_sig_restrict                funpre
% 2.69/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/0.98  --abstr_ref_under                       []
% 2.69/0.98  
% 2.69/0.98  ------ SAT Options
% 2.69/0.98  
% 2.69/0.98  --sat_mode                              false
% 2.69/0.98  --sat_fm_restart_options                ""
% 2.69/0.98  --sat_gr_def                            false
% 2.69/0.98  --sat_epr_types                         true
% 2.69/0.98  --sat_non_cyclic_types                  false
% 2.69/0.98  --sat_finite_models                     false
% 2.69/0.98  --sat_fm_lemmas                         false
% 2.69/0.98  --sat_fm_prep                           false
% 2.69/0.98  --sat_fm_uc_incr                        true
% 2.69/0.98  --sat_out_model                         small
% 2.69/0.98  --sat_out_clauses                       false
% 2.69/0.98  
% 2.69/0.98  ------ QBF Options
% 2.69/0.98  
% 2.69/0.98  --qbf_mode                              false
% 2.69/0.98  --qbf_elim_univ                         false
% 2.69/0.98  --qbf_dom_inst                          none
% 2.69/0.98  --qbf_dom_pre_inst                      false
% 2.69/0.98  --qbf_sk_in                             false
% 2.69/0.98  --qbf_pred_elim                         true
% 2.69/0.98  --qbf_split                             512
% 2.69/0.98  
% 2.69/0.98  ------ BMC1 Options
% 2.69/0.98  
% 2.69/0.98  --bmc1_incremental                      false
% 2.69/0.98  --bmc1_axioms                           reachable_all
% 2.69/0.98  --bmc1_min_bound                        0
% 2.69/0.98  --bmc1_max_bound                        -1
% 2.69/0.98  --bmc1_max_bound_default                -1
% 2.69/0.98  --bmc1_symbol_reachability              true
% 2.69/0.98  --bmc1_property_lemmas                  false
% 2.69/0.98  --bmc1_k_induction                      false
% 2.69/0.98  --bmc1_non_equiv_states                 false
% 2.69/0.98  --bmc1_deadlock                         false
% 2.69/0.98  --bmc1_ucm                              false
% 2.69/0.98  --bmc1_add_unsat_core                   none
% 2.69/0.98  --bmc1_unsat_core_children              false
% 2.69/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/0.98  --bmc1_out_stat                         full
% 2.69/0.98  --bmc1_ground_init                      false
% 2.69/0.98  --bmc1_pre_inst_next_state              false
% 2.69/0.98  --bmc1_pre_inst_state                   false
% 2.69/0.98  --bmc1_pre_inst_reach_state             false
% 2.69/0.98  --bmc1_out_unsat_core                   false
% 2.69/0.98  --bmc1_aig_witness_out                  false
% 2.69/0.98  --bmc1_verbose                          false
% 2.69/0.98  --bmc1_dump_clauses_tptp                false
% 2.69/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.69/0.98  --bmc1_dump_file                        -
% 2.69/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.69/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.69/0.98  --bmc1_ucm_extend_mode                  1
% 2.69/0.98  --bmc1_ucm_init_mode                    2
% 2.69/0.98  --bmc1_ucm_cone_mode                    none
% 2.69/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.69/0.98  --bmc1_ucm_relax_model                  4
% 2.69/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.69/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/0.98  --bmc1_ucm_layered_model                none
% 2.69/0.98  --bmc1_ucm_max_lemma_size               10
% 2.69/0.98  
% 2.69/0.98  ------ AIG Options
% 2.69/0.98  
% 2.69/0.98  --aig_mode                              false
% 2.69/0.98  
% 2.69/0.98  ------ Instantiation Options
% 2.69/0.98  
% 2.69/0.98  --instantiation_flag                    true
% 2.69/0.98  --inst_sos_flag                         false
% 2.69/0.98  --inst_sos_phase                        true
% 2.69/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/0.98  --inst_lit_sel_side                     num_symb
% 2.69/0.98  --inst_solver_per_active                1400
% 2.69/0.98  --inst_solver_calls_frac                1.
% 2.69/0.98  --inst_passive_queue_type               priority_queues
% 2.69/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/0.98  --inst_passive_queues_freq              [25;2]
% 2.69/0.98  --inst_dismatching                      true
% 2.69/0.98  --inst_eager_unprocessed_to_passive     true
% 2.69/0.98  --inst_prop_sim_given                   true
% 2.69/0.98  --inst_prop_sim_new                     false
% 2.69/0.98  --inst_subs_new                         false
% 2.69/0.98  --inst_eq_res_simp                      false
% 2.69/0.98  --inst_subs_given                       false
% 2.69/0.98  --inst_orphan_elimination               true
% 2.69/0.98  --inst_learning_loop_flag               true
% 2.69/0.98  --inst_learning_start                   3000
% 2.69/0.98  --inst_learning_factor                  2
% 2.69/0.98  --inst_start_prop_sim_after_learn       3
% 2.69/0.98  --inst_sel_renew                        solver
% 2.69/0.98  --inst_lit_activity_flag                true
% 2.69/0.98  --inst_restr_to_given                   false
% 2.69/0.98  --inst_activity_threshold               500
% 2.69/0.98  --inst_out_proof                        true
% 2.69/0.98  
% 2.69/0.98  ------ Resolution Options
% 2.69/0.98  
% 2.69/0.98  --resolution_flag                       true
% 2.69/0.98  --res_lit_sel                           adaptive
% 2.69/0.98  --res_lit_sel_side                      none
% 2.69/0.98  --res_ordering                          kbo
% 2.69/0.98  --res_to_prop_solver                    active
% 2.69/0.98  --res_prop_simpl_new                    false
% 2.69/0.98  --res_prop_simpl_given                  true
% 2.69/0.98  --res_passive_queue_type                priority_queues
% 2.69/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/0.98  --res_passive_queues_freq               [15;5]
% 2.69/0.98  --res_forward_subs                      full
% 2.69/0.98  --res_backward_subs                     full
% 2.69/0.98  --res_forward_subs_resolution           true
% 2.69/0.98  --res_backward_subs_resolution          true
% 2.69/0.98  --res_orphan_elimination                true
% 2.69/0.98  --res_time_limit                        2.
% 2.69/0.98  --res_out_proof                         true
% 2.69/0.98  
% 2.69/0.98  ------ Superposition Options
% 2.69/0.98  
% 2.69/0.98  --superposition_flag                    true
% 2.69/0.98  --sup_passive_queue_type                priority_queues
% 2.69/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.69/0.98  --demod_completeness_check              fast
% 2.69/0.98  --demod_use_ground                      true
% 2.69/0.98  --sup_to_prop_solver                    passive
% 2.69/0.98  --sup_prop_simpl_new                    true
% 2.69/0.98  --sup_prop_simpl_given                  true
% 2.69/0.98  --sup_fun_splitting                     false
% 2.69/0.98  --sup_smt_interval                      50000
% 2.69/0.98  
% 2.69/0.98  ------ Superposition Simplification Setup
% 2.69/0.98  
% 2.69/0.98  --sup_indices_passive                   []
% 2.69/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.98  --sup_full_bw                           [BwDemod]
% 2.69/0.98  --sup_immed_triv                        [TrivRules]
% 2.69/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.98  --sup_immed_bw_main                     []
% 2.69/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.98  
% 2.69/0.98  ------ Combination Options
% 2.69/0.98  
% 2.69/0.98  --comb_res_mult                         3
% 2.69/0.98  --comb_sup_mult                         2
% 2.69/0.98  --comb_inst_mult                        10
% 2.69/0.98  
% 2.69/0.98  ------ Debug Options
% 2.69/0.98  
% 2.69/0.98  --dbg_backtrace                         false
% 2.69/0.98  --dbg_dump_prop_clauses                 false
% 2.69/0.98  --dbg_dump_prop_clauses_file            -
% 2.69/0.98  --dbg_out_stat                          false
% 2.69/0.98  ------ Parsing...
% 2.69/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/0.98  
% 2.69/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.69/0.98  
% 2.69/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/0.98  
% 2.69/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.69/0.98  ------ Proving...
% 2.69/0.98  ------ Problem Properties 
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  clauses                                 32
% 2.69/0.98  conjectures                             17
% 2.69/0.98  EPR                                     21
% 2.69/0.98  Horn                                    25
% 2.69/0.98  unary                                   16
% 2.69/0.98  binary                                  2
% 2.69/0.98  lits                                    98
% 2.69/0.98  lits eq                                 5
% 2.69/0.98  fd_pure                                 0
% 2.69/0.98  fd_pseudo                               0
% 2.69/0.98  fd_cond                                 0
% 2.69/0.98  fd_pseudo_cond                          1
% 2.69/0.98  AC symbols                              0
% 2.69/0.98  
% 2.69/0.98  ------ Schedule dynamic 5 is on 
% 2.69/0.98  
% 2.69/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  ------ 
% 2.69/0.98  Current options:
% 2.69/0.98  ------ 
% 2.69/0.98  
% 2.69/0.98  ------ Input Options
% 2.69/0.98  
% 2.69/0.98  --out_options                           all
% 2.69/0.98  --tptp_safe_out                         true
% 2.69/0.98  --problem_path                          ""
% 2.69/0.98  --include_path                          ""
% 2.69/0.98  --clausifier                            res/vclausify_rel
% 2.69/0.98  --clausifier_options                    --mode clausify
% 2.69/0.98  --stdin                                 false
% 2.69/0.98  --stats_out                             all
% 2.69/0.98  
% 2.69/0.98  ------ General Options
% 2.69/0.98  
% 2.69/0.98  --fof                                   false
% 2.69/0.98  --time_out_real                         305.
% 2.69/0.98  --time_out_virtual                      -1.
% 2.69/0.98  --symbol_type_check                     false
% 2.69/0.98  --clausify_out                          false
% 2.69/0.98  --sig_cnt_out                           false
% 2.69/0.98  --trig_cnt_out                          false
% 2.69/0.98  --trig_cnt_out_tolerance                1.
% 2.69/0.98  --trig_cnt_out_sk_spl                   false
% 2.69/0.98  --abstr_cl_out                          false
% 2.69/0.98  
% 2.69/0.98  ------ Global Options
% 2.69/0.98  
% 2.69/0.98  --schedule                              default
% 2.69/0.98  --add_important_lit                     false
% 2.69/0.98  --prop_solver_per_cl                    1000
% 2.69/0.98  --min_unsat_core                        false
% 2.69/0.98  --soft_assumptions                      false
% 2.69/0.98  --soft_lemma_size                       3
% 2.69/0.98  --prop_impl_unit_size                   0
% 2.69/0.98  --prop_impl_unit                        []
% 2.69/0.98  --share_sel_clauses                     true
% 2.69/0.98  --reset_solvers                         false
% 2.69/0.98  --bc_imp_inh                            [conj_cone]
% 2.69/0.98  --conj_cone_tolerance                   3.
% 2.69/0.98  --extra_neg_conj                        none
% 2.69/0.98  --large_theory_mode                     true
% 2.69/0.98  --prolific_symb_bound                   200
% 2.69/0.98  --lt_threshold                          2000
% 2.69/0.98  --clause_weak_htbl                      true
% 2.69/0.98  --gc_record_bc_elim                     false
% 2.69/0.98  
% 2.69/0.98  ------ Preprocessing Options
% 2.69/0.98  
% 2.69/0.98  --preprocessing_flag                    true
% 2.69/0.98  --time_out_prep_mult                    0.1
% 2.69/0.98  --splitting_mode                        input
% 2.69/0.98  --splitting_grd                         true
% 2.69/0.98  --splitting_cvd                         false
% 2.69/0.98  --splitting_cvd_svl                     false
% 2.69/0.98  --splitting_nvd                         32
% 2.69/0.98  --sub_typing                            true
% 2.69/0.98  --prep_gs_sim                           true
% 2.69/0.98  --prep_unflatten                        true
% 2.69/0.98  --prep_res_sim                          true
% 2.69/0.98  --prep_upred                            true
% 2.69/0.98  --prep_sem_filter                       exhaustive
% 2.69/0.98  --prep_sem_filter_out                   false
% 2.69/0.98  --pred_elim                             true
% 2.69/0.98  --res_sim_input                         true
% 2.69/0.98  --eq_ax_congr_red                       true
% 2.69/0.98  --pure_diseq_elim                       true
% 2.69/0.98  --brand_transform                       false
% 2.69/0.98  --non_eq_to_eq                          false
% 2.69/0.98  --prep_def_merge                        true
% 2.69/0.98  --prep_def_merge_prop_impl              false
% 2.69/0.98  --prep_def_merge_mbd                    true
% 2.69/0.98  --prep_def_merge_tr_red                 false
% 2.69/0.98  --prep_def_merge_tr_cl                  false
% 2.69/0.98  --smt_preprocessing                     true
% 2.69/0.98  --smt_ac_axioms                         fast
% 2.69/0.98  --preprocessed_out                      false
% 2.69/0.98  --preprocessed_stats                    false
% 2.69/0.98  
% 2.69/0.98  ------ Abstraction refinement Options
% 2.69/0.98  
% 2.69/0.98  --abstr_ref                             []
% 2.69/0.98  --abstr_ref_prep                        false
% 2.69/0.98  --abstr_ref_until_sat                   false
% 2.69/0.98  --abstr_ref_sig_restrict                funpre
% 2.69/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/0.98  --abstr_ref_under                       []
% 2.69/0.98  
% 2.69/0.98  ------ SAT Options
% 2.69/0.98  
% 2.69/0.98  --sat_mode                              false
% 2.69/0.98  --sat_fm_restart_options                ""
% 2.69/0.98  --sat_gr_def                            false
% 2.69/0.98  --sat_epr_types                         true
% 2.69/0.98  --sat_non_cyclic_types                  false
% 2.69/0.98  --sat_finite_models                     false
% 2.69/0.98  --sat_fm_lemmas                         false
% 2.69/0.98  --sat_fm_prep                           false
% 2.69/0.98  --sat_fm_uc_incr                        true
% 2.69/0.98  --sat_out_model                         small
% 2.69/0.98  --sat_out_clauses                       false
% 2.69/0.98  
% 2.69/0.98  ------ QBF Options
% 2.69/0.98  
% 2.69/0.98  --qbf_mode                              false
% 2.69/0.98  --qbf_elim_univ                         false
% 2.69/0.98  --qbf_dom_inst                          none
% 2.69/0.98  --qbf_dom_pre_inst                      false
% 2.69/0.98  --qbf_sk_in                             false
% 2.69/0.98  --qbf_pred_elim                         true
% 2.69/0.98  --qbf_split                             512
% 2.69/0.98  
% 2.69/0.98  ------ BMC1 Options
% 2.69/0.98  
% 2.69/0.98  --bmc1_incremental                      false
% 2.69/0.98  --bmc1_axioms                           reachable_all
% 2.69/0.98  --bmc1_min_bound                        0
% 2.69/0.98  --bmc1_max_bound                        -1
% 2.69/0.98  --bmc1_max_bound_default                -1
% 2.69/0.98  --bmc1_symbol_reachability              true
% 2.69/0.98  --bmc1_property_lemmas                  false
% 2.69/0.98  --bmc1_k_induction                      false
% 2.69/0.98  --bmc1_non_equiv_states                 false
% 2.69/0.98  --bmc1_deadlock                         false
% 2.69/0.98  --bmc1_ucm                              false
% 2.69/0.98  --bmc1_add_unsat_core                   none
% 2.69/0.98  --bmc1_unsat_core_children              false
% 2.69/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/0.98  --bmc1_out_stat                         full
% 2.69/0.98  --bmc1_ground_init                      false
% 2.69/0.98  --bmc1_pre_inst_next_state              false
% 2.69/0.98  --bmc1_pre_inst_state                   false
% 2.69/0.98  --bmc1_pre_inst_reach_state             false
% 2.69/0.98  --bmc1_out_unsat_core                   false
% 2.69/0.98  --bmc1_aig_witness_out                  false
% 2.69/0.98  --bmc1_verbose                          false
% 2.69/0.98  --bmc1_dump_clauses_tptp                false
% 2.69/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.69/0.98  --bmc1_dump_file                        -
% 2.69/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.69/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.69/0.98  --bmc1_ucm_extend_mode                  1
% 2.69/0.98  --bmc1_ucm_init_mode                    2
% 2.69/0.98  --bmc1_ucm_cone_mode                    none
% 2.69/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.69/0.98  --bmc1_ucm_relax_model                  4
% 2.69/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.69/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/0.98  --bmc1_ucm_layered_model                none
% 2.69/0.98  --bmc1_ucm_max_lemma_size               10
% 2.69/0.98  
% 2.69/0.98  ------ AIG Options
% 2.69/0.98  
% 2.69/0.98  --aig_mode                              false
% 2.69/0.98  
% 2.69/0.98  ------ Instantiation Options
% 2.69/0.98  
% 2.69/0.98  --instantiation_flag                    true
% 2.69/0.98  --inst_sos_flag                         false
% 2.69/0.98  --inst_sos_phase                        true
% 2.69/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/0.98  --inst_lit_sel_side                     none
% 2.69/0.98  --inst_solver_per_active                1400
% 2.69/0.98  --inst_solver_calls_frac                1.
% 2.69/0.98  --inst_passive_queue_type               priority_queues
% 2.69/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/0.98  --inst_passive_queues_freq              [25;2]
% 2.69/0.98  --inst_dismatching                      true
% 2.69/0.98  --inst_eager_unprocessed_to_passive     true
% 2.69/0.98  --inst_prop_sim_given                   true
% 2.69/0.98  --inst_prop_sim_new                     false
% 2.69/0.98  --inst_subs_new                         false
% 2.69/0.98  --inst_eq_res_simp                      false
% 2.69/0.98  --inst_subs_given                       false
% 2.69/0.98  --inst_orphan_elimination               true
% 2.69/0.98  --inst_learning_loop_flag               true
% 2.69/0.98  --inst_learning_start                   3000
% 2.69/0.98  --inst_learning_factor                  2
% 2.69/0.98  --inst_start_prop_sim_after_learn       3
% 2.69/0.98  --inst_sel_renew                        solver
% 2.69/0.98  --inst_lit_activity_flag                true
% 2.69/0.98  --inst_restr_to_given                   false
% 2.69/0.98  --inst_activity_threshold               500
% 2.69/0.98  --inst_out_proof                        true
% 2.69/0.98  
% 2.69/0.98  ------ Resolution Options
% 2.69/0.98  
% 2.69/0.98  --resolution_flag                       false
% 2.69/0.98  --res_lit_sel                           adaptive
% 2.69/0.98  --res_lit_sel_side                      none
% 2.69/0.98  --res_ordering                          kbo
% 2.69/0.98  --res_to_prop_solver                    active
% 2.69/0.98  --res_prop_simpl_new                    false
% 2.69/0.98  --res_prop_simpl_given                  true
% 2.69/0.98  --res_passive_queue_type                priority_queues
% 2.69/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/0.98  --res_passive_queues_freq               [15;5]
% 2.69/0.98  --res_forward_subs                      full
% 2.69/0.98  --res_backward_subs                     full
% 2.69/0.98  --res_forward_subs_resolution           true
% 2.69/0.98  --res_backward_subs_resolution          true
% 2.69/0.98  --res_orphan_elimination                true
% 2.69/0.98  --res_time_limit                        2.
% 2.69/0.98  --res_out_proof                         true
% 2.69/0.98  
% 2.69/0.98  ------ Superposition Options
% 2.69/0.98  
% 2.69/0.98  --superposition_flag                    true
% 2.69/0.98  --sup_passive_queue_type                priority_queues
% 2.69/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.69/0.98  --demod_completeness_check              fast
% 2.69/0.98  --demod_use_ground                      true
% 2.69/0.98  --sup_to_prop_solver                    passive
% 2.69/0.98  --sup_prop_simpl_new                    true
% 2.69/0.98  --sup_prop_simpl_given                  true
% 2.69/0.98  --sup_fun_splitting                     false
% 2.69/0.98  --sup_smt_interval                      50000
% 2.69/0.98  
% 2.69/0.98  ------ Superposition Simplification Setup
% 2.69/0.98  
% 2.69/0.98  --sup_indices_passive                   []
% 2.69/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.98  --sup_full_bw                           [BwDemod]
% 2.69/0.98  --sup_immed_triv                        [TrivRules]
% 2.69/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.98  --sup_immed_bw_main                     []
% 2.69/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.98  
% 2.69/0.98  ------ Combination Options
% 2.69/0.98  
% 2.69/0.98  --comb_res_mult                         3
% 2.69/0.98  --comb_sup_mult                         2
% 2.69/0.98  --comb_inst_mult                        10
% 2.69/0.98  
% 2.69/0.98  ------ Debug Options
% 2.69/0.98  
% 2.69/0.98  --dbg_backtrace                         false
% 2.69/0.98  --dbg_dump_prop_clauses                 false
% 2.69/0.98  --dbg_dump_prop_clauses_file            -
% 2.69/0.98  --dbg_out_stat                          false
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  ------ Proving...
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  % SZS status Theorem for theBenchmark.p
% 2.69/0.98  
% 2.69/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/0.98  
% 2.69/0.98  fof(f14,conjecture,(
% 2.69/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 2.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f15,negated_conjecture,(
% 2.69/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 2.69/0.98    inference(negated_conjecture,[],[f14])).
% 2.69/0.98  
% 2.69/0.98  fof(f36,plain,(
% 2.69/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.69/0.98    inference(ennf_transformation,[],[f15])).
% 2.69/0.98  
% 2.69/0.98  fof(f37,plain,(
% 2.69/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.69/0.98    inference(flattening,[],[f36])).
% 2.69/0.98  
% 2.69/0.98  fof(f46,plain,(
% 2.69/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.69/0.98    inference(nnf_transformation,[],[f37])).
% 2.69/0.98  
% 2.69/0.98  fof(f47,plain,(
% 2.69/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.69/0.98    inference(flattening,[],[f46])).
% 2.69/0.98  
% 2.69/0.98  fof(f54,plain,(
% 2.69/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) | r1_tmap_1(X3,X1,X4,X5)) & sK7 = X5 & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.69/0.98    introduced(choice_axiom,[])).
% 2.69/0.98  
% 2.69/0.98  fof(f53,plain,(
% 2.69/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,sK6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,sK6)) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.69/0.98    introduced(choice_axiom,[])).
% 2.69/0.98  
% 2.69/0.98  fof(f52,plain,(
% 2.69/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6) | ~r1_tmap_1(X3,X1,sK5,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6) | r1_tmap_1(X3,X1,sK5,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.69/0.98    introduced(choice_axiom,[])).
% 2.69/0.98  
% 2.69/0.98  fof(f51,plain,(
% 2.69/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6) | ~r1_tmap_1(sK4,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6) | r1_tmap_1(sK4,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_pre_topc(X2,sK4) & v1_tsep_1(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.69/0.98    introduced(choice_axiom,[])).
% 2.69/0.98  
% 2.69/0.98  fof(f50,plain,(
% 2.69/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK3,X3) & v1_tsep_1(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.69/0.98    introduced(choice_axiom,[])).
% 2.69/0.98  
% 2.69/0.98  fof(f49,plain,(
% 2.69/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK2,X4,X5)) & (r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6) | r1_tmap_1(X3,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.69/0.98    introduced(choice_axiom,[])).
% 2.69/0.98  
% 2.69/0.98  fof(f48,plain,(
% 2.69/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.69/0.98    introduced(choice_axiom,[])).
% 2.69/0.98  
% 2.69/0.98  fof(f55,plain,(
% 2.69/0.98    (((((((~r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) | ~r1_tmap_1(sK4,sK2,sK5,sK6)) & (r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) | r1_tmap_1(sK4,sK2,sK5,sK6)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_pre_topc(sK3,sK4) & v1_tsep_1(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.69/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f47,f54,f53,f52,f51,f50,f49,f48])).
% 2.69/0.98  
% 2.69/0.98  fof(f93,plain,(
% 2.69/0.98    m1_subset_1(sK7,u1_struct_0(sK3))),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f8,axiom,(
% 2.69/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 2.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f25,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.69/0.98    inference(ennf_transformation,[],[f8])).
% 2.69/0.98  
% 2.69/0.98  fof(f26,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.69/0.98    inference(flattening,[],[f25])).
% 2.69/0.98  
% 2.69/0.98  fof(f68,plain,(
% 2.69/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f26])).
% 2.69/0.98  
% 2.69/0.98  fof(f6,axiom,(
% 2.69/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f21,plain,(
% 2.69/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.69/0.98    inference(ennf_transformation,[],[f6])).
% 2.69/0.98  
% 2.69/0.98  fof(f22,plain,(
% 2.69/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.69/0.98    inference(flattening,[],[f21])).
% 2.69/0.98  
% 2.69/0.98  fof(f66,plain,(
% 2.69/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f22])).
% 2.69/0.98  
% 2.69/0.98  fof(f7,axiom,(
% 2.69/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 2.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f23,plain,(
% 2.69/0.98    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.69/0.98    inference(ennf_transformation,[],[f7])).
% 2.69/0.98  
% 2.69/0.98  fof(f24,plain,(
% 2.69/0.98    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.69/0.98    inference(flattening,[],[f23])).
% 2.69/0.98  
% 2.69/0.98  fof(f41,plain,(
% 2.69/0.98    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 2.69/0.98    introduced(choice_axiom,[])).
% 2.69/0.98  
% 2.69/0.98  fof(f42,plain,(
% 2.69/0.98    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.69/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f41])).
% 2.69/0.98  
% 2.69/0.98  fof(f67,plain,(
% 2.69/0.98    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f42])).
% 2.69/0.98  
% 2.69/0.98  fof(f3,axiom,(
% 2.69/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f17,plain,(
% 2.69/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.69/0.98    inference(ennf_transformation,[],[f3])).
% 2.69/0.98  
% 2.69/0.98  fof(f63,plain,(
% 2.69/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f17])).
% 2.69/0.98  
% 2.69/0.98  fof(f4,axiom,(
% 2.69/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f18,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.69/0.98    inference(ennf_transformation,[],[f4])).
% 2.69/0.98  
% 2.69/0.98  fof(f19,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.69/0.98    inference(flattening,[],[f18])).
% 2.69/0.98  
% 2.69/0.98  fof(f64,plain,(
% 2.69/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f19])).
% 2.69/0.98  
% 2.69/0.98  fof(f13,axiom,(
% 2.69/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f34,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.69/0.98    inference(ennf_transformation,[],[f13])).
% 2.69/0.98  
% 2.69/0.98  fof(f35,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.69/0.98    inference(flattening,[],[f34])).
% 2.69/0.98  
% 2.69/0.98  fof(f45,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.69/0.98    inference(nnf_transformation,[],[f35])).
% 2.69/0.98  
% 2.69/0.98  fof(f75,plain,(
% 2.69/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f45])).
% 2.69/0.98  
% 2.69/0.98  fof(f104,plain,(
% 2.69/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.69/0.98    inference(equality_resolution,[],[f75])).
% 2.69/0.98  
% 2.69/0.98  fof(f12,axiom,(
% 2.69/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 2.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f32,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.69/0.98    inference(ennf_transformation,[],[f12])).
% 2.69/0.98  
% 2.69/0.98  fof(f33,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.69/0.98    inference(flattening,[],[f32])).
% 2.69/0.98  
% 2.69/0.98  fof(f74,plain,(
% 2.69/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f33])).
% 2.69/0.98  
% 2.69/0.98  fof(f102,plain,(
% 2.69/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.69/0.98    inference(equality_resolution,[],[f74])).
% 2.69/0.98  
% 2.69/0.98  fof(f88,plain,(
% 2.69/0.98    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f87,plain,(
% 2.69/0.98    v1_funct_1(sK5)),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f11,axiom,(
% 2.69/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f30,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.69/0.98    inference(ennf_transformation,[],[f11])).
% 2.69/0.98  
% 2.69/0.98  fof(f31,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.69/0.98    inference(flattening,[],[f30])).
% 2.69/0.98  
% 2.69/0.98  fof(f73,plain,(
% 2.69/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f31])).
% 2.69/0.98  
% 2.69/0.98  fof(f85,plain,(
% 2.69/0.98    ~v2_struct_0(sK4)),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f80,plain,(
% 2.69/0.98    ~v2_struct_0(sK2)),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f81,plain,(
% 2.69/0.98    v2_pre_topc(sK2)),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f82,plain,(
% 2.69/0.98    l1_pre_topc(sK2)),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f89,plain,(
% 2.69/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f96,plain,(
% 2.69/0.98    ~r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) | ~r1_tmap_1(sK4,sK2,sK5,sK6)),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f94,plain,(
% 2.69/0.98    sK6 = sK7),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f95,plain,(
% 2.69/0.98    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) | r1_tmap_1(sK4,sK2,sK5,sK6)),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f76,plain,(
% 2.69/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f45])).
% 2.69/0.98  
% 2.69/0.98  fof(f103,plain,(
% 2.69/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.69/0.98    inference(equality_resolution,[],[f76])).
% 2.69/0.98  
% 2.69/0.98  fof(f9,axiom,(
% 2.69/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f27,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.69/0.98    inference(ennf_transformation,[],[f9])).
% 2.69/0.98  
% 2.69/0.98  fof(f28,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.69/0.98    inference(flattening,[],[f27])).
% 2.69/0.98  
% 2.69/0.98  fof(f43,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.69/0.98    inference(nnf_transformation,[],[f28])).
% 2.69/0.98  
% 2.69/0.98  fof(f44,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.69/0.98    inference(flattening,[],[f43])).
% 2.69/0.98  
% 2.69/0.98  fof(f69,plain,(
% 2.69/0.98    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f44])).
% 2.69/0.98  
% 2.69/0.98  fof(f101,plain,(
% 2.69/0.98    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.69/0.98    inference(equality_resolution,[],[f69])).
% 2.69/0.98  
% 2.69/0.98  fof(f10,axiom,(
% 2.69/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f29,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.69/0.98    inference(ennf_transformation,[],[f10])).
% 2.69/0.98  
% 2.69/0.98  fof(f72,plain,(
% 2.69/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f29])).
% 2.69/0.98  
% 2.69/0.98  fof(f90,plain,(
% 2.69/0.98    v1_tsep_1(sK3,sK4)),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f91,plain,(
% 2.69/0.98    m1_pre_topc(sK3,sK4)),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f5,axiom,(
% 2.69/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f20,plain,(
% 2.69/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.69/0.98    inference(ennf_transformation,[],[f5])).
% 2.69/0.98  
% 2.69/0.98  fof(f65,plain,(
% 2.69/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f20])).
% 2.69/0.98  
% 2.69/0.98  fof(f79,plain,(
% 2.69/0.98    l1_pre_topc(sK1)),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f86,plain,(
% 2.69/0.98    m1_pre_topc(sK4,sK1)),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f77,plain,(
% 2.69/0.98    ~v2_struct_0(sK1)),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f78,plain,(
% 2.69/0.98    v2_pre_topc(sK1)),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f83,plain,(
% 2.69/0.98    ~v2_struct_0(sK3)),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f92,plain,(
% 2.69/0.98    m1_subset_1(sK6,u1_struct_0(sK4))),
% 2.69/0.98    inference(cnf_transformation,[],[f55])).
% 2.69/0.98  
% 2.69/0.98  fof(f1,axiom,(
% 2.69/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f38,plain,(
% 2.69/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.69/0.98    inference(nnf_transformation,[],[f1])).
% 2.69/0.98  
% 2.69/0.98  fof(f39,plain,(
% 2.69/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.69/0.98    inference(flattening,[],[f38])).
% 2.69/0.98  
% 2.69/0.98  fof(f57,plain,(
% 2.69/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.69/0.98    inference(cnf_transformation,[],[f39])).
% 2.69/0.98  
% 2.69/0.98  fof(f97,plain,(
% 2.69/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.69/0.98    inference(equality_resolution,[],[f57])).
% 2.69/0.98  
% 2.69/0.98  fof(f2,axiom,(
% 2.69/0.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f16,plain,(
% 2.69/0.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.69/0.98    inference(ennf_transformation,[],[f2])).
% 2.69/0.98  
% 2.69/0.98  fof(f40,plain,(
% 2.69/0.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.69/0.98    inference(nnf_transformation,[],[f16])).
% 2.69/0.98  
% 2.69/0.98  fof(f59,plain,(
% 2.69/0.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f40])).
% 2.69/0.98  
% 2.69/0.98  cnf(c_24,negated_conjecture,
% 2.69/0.98      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.69/0.98      inference(cnf_transformation,[],[f93]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2311,plain,
% 2.69/0.98      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_12,plain,
% 2.69/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.69/0.98      | r2_hidden(X2,X0)
% 2.69/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.69/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_10,plain,
% 2.69/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.69/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.69/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_234,plain,
% 2.69/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.69/0.98      | r2_hidden(X2,X0)
% 2.69/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X1) ),
% 2.69/0.98      inference(global_propositional_subsumption,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_12,c_10]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_235,plain,
% 2.69/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.69/0.98      | r2_hidden(X2,X0)
% 2.69/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X1) ),
% 2.69/0.98      inference(renaming,[status(thm)],[c_234]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_11,plain,
% 2.69/0.98      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 2.69/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | ~ l1_pre_topc(X0)
% 2.69/0.98      | ~ v2_pre_topc(X0) ),
% 2.69/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_531,plain,
% 2.69/0.98      ( r2_hidden(X0,X1)
% 2.69/0.98      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.69/0.98      | v2_struct_0(X2)
% 2.69/0.98      | v2_struct_0(X4)
% 2.69/0.98      | ~ l1_pre_topc(X2)
% 2.69/0.98      | ~ l1_pre_topc(X4)
% 2.69/0.98      | ~ v2_pre_topc(X2)
% 2.69/0.98      | ~ v2_pre_topc(X4)
% 2.69/0.98      | X4 != X2
% 2.69/0.98      | X3 != X0
% 2.69/0.98      | sK0(X4,X3) != X1 ),
% 2.69/0.98      inference(resolution_lifted,[status(thm)],[c_235,c_11]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_532,plain,
% 2.69/0.98      ( r2_hidden(X0,sK0(X1,X0))
% 2.69/0.98      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X1) ),
% 2.69/0.98      inference(unflattening,[status(thm)],[c_531]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2297,plain,
% 2.69/0.98      ( r2_hidden(X0,sK0(X1,X0)) = iProver_top
% 2.69/0.98      | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | l1_pre_topc(X1) != iProver_top
% 2.69/0.98      | v2_pre_topc(X1) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_532]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_552,plain,
% 2.69/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.69/0.98      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 2.69/0.98      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X3)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X3)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X3)
% 2.69/0.98      | X3 != X1
% 2.69/0.98      | X2 != X0
% 2.69/0.98      | sK0(X3,X2) != X4 ),
% 2.69/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_11]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_553,plain,
% 2.69/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.69/0.98      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X1) ),
% 2.69/0.98      inference(unflattening,[status(thm)],[c_552]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2296,plain,
% 2.69/0.98      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 2.69/0.98      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | l1_pre_topc(X1) != iProver_top
% 2.69/0.98      | v2_pre_topc(X1) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_553]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_7,plain,
% 2.69/0.98      ( ~ r2_hidden(X0,X1)
% 2.69/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.69/0.98      | ~ v1_xboole_0(X2) ),
% 2.69/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2318,plain,
% 2.69/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.69/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 2.69/0.98      | v1_xboole_0(X2) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3856,plain,
% 2.69/0.98      ( r2_hidden(X0,sK0(X1,X2)) != iProver_top
% 2.69/0.98      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | l1_pre_topc(X1) != iProver_top
% 2.69/0.98      | v2_pre_topc(X1) != iProver_top
% 2.69/0.98      | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_2296,c_2318]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_5086,plain,
% 2.69/0.98      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | l1_pre_topc(X1) != iProver_top
% 2.69/0.98      | v2_pre_topc(X1) != iProver_top
% 2.69/0.98      | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_2297,c_3856]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_5140,plain,
% 2.69/0.98      ( v2_struct_0(sK3) = iProver_top
% 2.69/0.98      | l1_pre_topc(sK3) != iProver_top
% 2.69/0.98      | v2_pre_topc(sK3) != iProver_top
% 2.69/0.98      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_2311,c_5086]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_8,plain,
% 2.69/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | v2_pre_topc(X0) ),
% 2.69/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3534,plain,
% 2.69/0.98      ( ~ m1_pre_topc(sK3,X0)
% 2.69/0.98      | ~ l1_pre_topc(X0)
% 2.69/0.98      | ~ v2_pre_topc(X0)
% 2.69/0.98      | v2_pre_topc(sK3) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_4291,plain,
% 2.69/0.98      ( ~ m1_pre_topc(sK3,sK4)
% 2.69/0.98      | ~ l1_pre_topc(sK4)
% 2.69/0.98      | ~ v2_pre_topc(sK4)
% 2.69/0.98      | v2_pre_topc(sK3) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_3534]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_4292,plain,
% 2.69/0.98      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.69/0.98      | l1_pre_topc(sK4) != iProver_top
% 2.69/0.98      | v2_pre_topc(sK4) != iProver_top
% 2.69/0.98      | v2_pre_topc(sK3) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_4291]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_20,plain,
% 2.69/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.69/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.69/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.69/0.98      | ~ v3_pre_topc(X6,X0)
% 2.69/0.98      | ~ m1_pre_topc(X4,X5)
% 2.69/0.98      | ~ m1_pre_topc(X0,X5)
% 2.69/0.98      | ~ m1_pre_topc(X4,X0)
% 2.69/0.98      | ~ r2_hidden(X3,X6)
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.69/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.69/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.69/0.98      | ~ v1_funct_1(X2)
% 2.69/0.98      | v2_struct_0(X5)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X4)
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | ~ l1_pre_topc(X5)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X5)
% 2.69/0.98      | ~ v2_pre_topc(X1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f104]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_18,plain,
% 2.69/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.69/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.69/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.69/0.98      | ~ m1_pre_topc(X0,X5)
% 2.69/0.98      | ~ m1_pre_topc(X4,X0)
% 2.69/0.98      | ~ m1_pre_topc(X4,X5)
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.69/0.98      | ~ v1_funct_1(X2)
% 2.69/0.98      | v2_struct_0(X5)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | v2_struct_0(X4)
% 2.69/0.98      | ~ l1_pre_topc(X5)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X5)
% 2.69/0.98      | ~ v2_pre_topc(X1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f102]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_211,plain,
% 2.69/0.98      ( ~ m1_pre_topc(X4,X0)
% 2.69/0.98      | ~ m1_pre_topc(X0,X5)
% 2.69/0.98      | ~ m1_pre_topc(X4,X5)
% 2.69/0.98      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.69/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.69/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.69/0.98      | ~ v1_funct_1(X2)
% 2.69/0.98      | v2_struct_0(X5)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X4)
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | ~ l1_pre_topc(X5)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X5)
% 2.69/0.98      | ~ v2_pre_topc(X1) ),
% 2.69/0.98      inference(global_propositional_subsumption,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_20,c_18]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_212,plain,
% 2.69/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.69/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.69/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.69/0.98      | ~ m1_pre_topc(X0,X5)
% 2.69/0.98      | ~ m1_pre_topc(X4,X0)
% 2.69/0.98      | ~ m1_pre_topc(X4,X5)
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.69/0.98      | ~ v1_funct_1(X2)
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X5)
% 2.69/0.98      | v2_struct_0(X4)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X5)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X5) ),
% 2.69/0.98      inference(renaming,[status(thm)],[c_211]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_29,negated_conjecture,
% 2.69/0.98      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 2.69/0.98      inference(cnf_transformation,[],[f88]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_664,plain,
% 2.69/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.69/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.69/0.98      | ~ m1_pre_topc(X0,X5)
% 2.69/0.98      | ~ m1_pre_topc(X4,X0)
% 2.69/0.98      | ~ m1_pre_topc(X4,X5)
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.69/0.98      | ~ v1_funct_1(X2)
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X5)
% 2.69/0.98      | v2_struct_0(X4)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X5)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X5)
% 2.69/0.98      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.69/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.69/0.98      | sK5 != X2 ),
% 2.69/0.98      inference(resolution_lifted,[status(thm)],[c_212,c_29]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_665,plain,
% 2.69/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.69/0.98      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.69/0.98      | ~ m1_pre_topc(X3,X2)
% 2.69/0.98      | ~ m1_pre_topc(X0,X3)
% 2.69/0.98      | ~ m1_pre_topc(X0,X2)
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.69/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.69/0.98      | ~ v1_funct_1(sK5)
% 2.69/0.98      | v2_struct_0(X3)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X2)
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X2)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X2)
% 2.69/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.69/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.69/0.98      inference(unflattening,[status(thm)],[c_664]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_30,negated_conjecture,
% 2.69/0.98      ( v1_funct_1(sK5) ),
% 2.69/0.98      inference(cnf_transformation,[],[f87]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_669,plain,
% 2.69/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_pre_topc(X0,X2)
% 2.69/0.98      | ~ m1_pre_topc(X0,X3)
% 2.69/0.98      | ~ m1_pre_topc(X3,X2)
% 2.69/0.98      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.69/0.98      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.69/0.98      | v2_struct_0(X3)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X2)
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X2)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X2)
% 2.69/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.69/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.69/0.98      inference(global_propositional_subsumption,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_665,c_30]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_670,plain,
% 2.69/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.69/0.98      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.69/0.98      | ~ m1_pre_topc(X3,X2)
% 2.69/0.98      | ~ m1_pre_topc(X0,X2)
% 2.69/0.98      | ~ m1_pre_topc(X0,X3)
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X2)
% 2.69/0.98      | v2_struct_0(X3)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X2)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X2)
% 2.69/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.69/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.69/0.98      inference(renaming,[status(thm)],[c_669]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_17,plain,
% 2.69/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.69/0.98      | ~ m1_pre_topc(X2,X0)
% 2.69/0.98      | m1_pre_topc(X2,X1)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_711,plain,
% 2.69/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.69/0.98      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.69/0.98      | ~ m1_pre_topc(X3,X2)
% 2.69/0.98      | ~ m1_pre_topc(X0,X3)
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X2)
% 2.69/0.98      | v2_struct_0(X3)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X2)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X2)
% 2.69/0.98      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.69/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.69/0.98      inference(forward_subsumption_resolution,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_670,c_17]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2295,plain,
% 2.69/0.98      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 2.69/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.69/0.98      | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) = iProver_top
% 2.69/0.98      | r1_tmap_1(X0,X1,sK5,X4) != iProver_top
% 2.69/0.98      | m1_pre_topc(X0,X3) != iProver_top
% 2.69/0.98      | m1_pre_topc(X2,X0) != iProver_top
% 2.69/0.98      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 2.69/0.98      | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
% 2.69/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | v2_struct_0(X2) = iProver_top
% 2.69/0.98      | v2_struct_0(X3) = iProver_top
% 2.69/0.98      | v2_struct_0(X0) = iProver_top
% 2.69/0.98      | l1_pre_topc(X1) != iProver_top
% 2.69/0.98      | l1_pre_topc(X3) != iProver_top
% 2.69/0.98      | v2_pre_topc(X1) != iProver_top
% 2.69/0.98      | v2_pre_topc(X3) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_711]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3098,plain,
% 2.69/0.98      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 2.69/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 2.69/0.98      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 2.69/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.69/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 2.69/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.69/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.69/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | v2_struct_0(X0) = iProver_top
% 2.69/0.98      | v2_struct_0(X2) = iProver_top
% 2.69/0.98      | v2_struct_0(sK4) = iProver_top
% 2.69/0.98      | l1_pre_topc(X0) != iProver_top
% 2.69/0.98      | l1_pre_topc(X2) != iProver_top
% 2.69/0.98      | v2_pre_topc(X0) != iProver_top
% 2.69/0.98      | v2_pre_topc(X2) != iProver_top ),
% 2.69/0.98      inference(equality_resolution,[status(thm)],[c_2295]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_32,negated_conjecture,
% 2.69/0.98      ( ~ v2_struct_0(sK4) ),
% 2.69/0.98      inference(cnf_transformation,[],[f85]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_49,plain,
% 2.69/0.98      ( v2_struct_0(sK4) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1513,plain,( X0 = X0 ),theory(equality) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2597,plain,
% 2.69/0.98      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_1513]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2598,plain,
% 2.69/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
% 2.69/0.98      | ~ r1_tmap_1(sK4,X1,sK5,X3)
% 2.69/0.98      | ~ m1_pre_topc(X0,sK4)
% 2.69/0.98      | ~ m1_pre_topc(sK4,X2)
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 2.69/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X2)
% 2.69/0.98      | v2_struct_0(sK4)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X2)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X2)
% 2.69/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.69/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_711]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2599,plain,
% 2.69/0.98      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 2.69/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.69/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 2.69/0.98      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 2.69/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.69/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 2.69/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.69/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.69/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.69/0.98      | v2_struct_0(X0) = iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | v2_struct_0(X2) = iProver_top
% 2.69/0.98      | v2_struct_0(sK4) = iProver_top
% 2.69/0.98      | l1_pre_topc(X0) != iProver_top
% 2.69/0.98      | l1_pre_topc(X2) != iProver_top
% 2.69/0.98      | v2_pre_topc(X0) != iProver_top
% 2.69/0.98      | v2_pre_topc(X2) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_2598]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3592,plain,
% 2.69/0.98      ( v2_struct_0(X2) = iProver_top
% 2.69/0.98      | v2_struct_0(X0) = iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.69/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.69/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.69/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 2.69/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.69/0.98      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 2.69/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 2.69/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.69/0.98      | l1_pre_topc(X0) != iProver_top
% 2.69/0.98      | l1_pre_topc(X2) != iProver_top
% 2.69/0.98      | v2_pre_topc(X0) != iProver_top
% 2.69/0.98      | v2_pre_topc(X2) != iProver_top ),
% 2.69/0.98      inference(global_propositional_subsumption,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_3098,c_49,c_2597,c_2599]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3593,plain,
% 2.69/0.98      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 2.69/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 2.69/0.98      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 2.69/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.69/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 2.69/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.69/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.69/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | v2_struct_0(X0) = iProver_top
% 2.69/0.98      | v2_struct_0(X2) = iProver_top
% 2.69/0.98      | l1_pre_topc(X0) != iProver_top
% 2.69/0.98      | l1_pre_topc(X2) != iProver_top
% 2.69/0.98      | v2_pre_topc(X0) != iProver_top
% 2.69/0.98      | v2_pre_topc(X2) != iProver_top ),
% 2.69/0.98      inference(renaming,[status(thm)],[c_3592]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3613,plain,
% 2.69/0.98      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
% 2.69/0.98      | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
% 2.69/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.69/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 2.69/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.69/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.69/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | v2_struct_0(X0) = iProver_top
% 2.69/0.98      | v2_struct_0(sK2) = iProver_top
% 2.69/0.98      | l1_pre_topc(X1) != iProver_top
% 2.69/0.98      | l1_pre_topc(sK2) != iProver_top
% 2.69/0.98      | v2_pre_topc(X1) != iProver_top
% 2.69/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 2.69/0.98      inference(equality_resolution,[status(thm)],[c_3593]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_37,negated_conjecture,
% 2.69/0.98      ( ~ v2_struct_0(sK2) ),
% 2.69/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_44,plain,
% 2.69/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_36,negated_conjecture,
% 2.69/0.98      ( v2_pre_topc(sK2) ),
% 2.69/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_45,plain,
% 2.69/0.98      ( v2_pre_topc(sK2) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_35,negated_conjecture,
% 2.69/0.98      ( l1_pre_topc(sK2) ),
% 2.69/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_46,plain,
% 2.69/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_28,negated_conjecture,
% 2.69/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 2.69/0.98      inference(cnf_transformation,[],[f89]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_53,plain,
% 2.69/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_4042,plain,
% 2.69/0.98      ( v2_pre_topc(X1) != iProver_top
% 2.69/0.98      | v2_struct_0(X0) = iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
% 2.69/0.98      | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
% 2.69/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.69/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 2.69/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.69/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.69/0.98      | l1_pre_topc(X1) != iProver_top ),
% 2.69/0.98      inference(global_propositional_subsumption,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_3613,c_44,c_45,c_46,c_53]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_4043,plain,
% 2.69/0.98      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) = iProver_top
% 2.69/0.98      | r1_tmap_1(sK4,sK2,sK5,X2) != iProver_top
% 2.69/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.69/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 2.69/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.69/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | v2_struct_0(X0) = iProver_top
% 2.69/0.98      | l1_pre_topc(X1) != iProver_top
% 2.69/0.98      | v2_pre_topc(X1) != iProver_top ),
% 2.69/0.98      inference(renaming,[status(thm)],[c_4042]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_21,negated_conjecture,
% 2.69/0.98      ( ~ r1_tmap_1(sK4,sK2,sK5,sK6)
% 2.69/0.98      | ~ r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
% 2.69/0.98      inference(cnf_transformation,[],[f96]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2313,plain,
% 2.69/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK6) != iProver_top
% 2.69/0.98      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_23,negated_conjecture,
% 2.69/0.98      ( sK6 = sK7 ),
% 2.69/0.98      inference(cnf_transformation,[],[f94]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2411,plain,
% 2.69/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
% 2.69/0.98      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) != iProver_top ),
% 2.69/0.98      inference(light_normalisation,[status(thm)],[c_2313,c_23]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_4058,plain,
% 2.69/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK7) != iProver_top
% 2.69/0.98      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.69/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.69/0.98      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 2.69/0.98      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.69/0.98      | v2_struct_0(sK1) = iProver_top
% 2.69/0.98      | v2_struct_0(sK3) = iProver_top
% 2.69/0.98      | l1_pre_topc(sK1) != iProver_top
% 2.69/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_4043,c_2411]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3157,plain,
% 2.69/0.98      ( ~ m1_pre_topc(sK4,X0)
% 2.69/0.98      | ~ l1_pre_topc(X0)
% 2.69/0.98      | ~ v2_pre_topc(X0)
% 2.69/0.98      | v2_pre_topc(sK4) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3749,plain,
% 2.69/0.98      ( ~ m1_pre_topc(sK4,sK1)
% 2.69/0.98      | ~ l1_pre_topc(sK1)
% 2.69/0.98      | v2_pre_topc(sK4)
% 2.69/0.98      | ~ v2_pre_topc(sK1) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_3157]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3750,plain,
% 2.69/0.98      ( m1_pre_topc(sK4,sK1) != iProver_top
% 2.69/0.98      | l1_pre_topc(sK1) != iProver_top
% 2.69/0.98      | v2_pre_topc(sK4) = iProver_top
% 2.69/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_3749]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_22,negated_conjecture,
% 2.69/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK6)
% 2.69/0.98      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
% 2.69/0.98      inference(cnf_transformation,[],[f95]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2312,plain,
% 2.69/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK6) = iProver_top
% 2.69/0.98      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2394,plain,
% 2.69/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
% 2.69/0.98      | r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
% 2.69/0.98      inference(light_normalisation,[status(thm)],[c_2312,c_23]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_19,plain,
% 2.69/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.69/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.69/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.69/0.98      | ~ v3_pre_topc(X6,X0)
% 2.69/0.98      | ~ m1_pre_topc(X4,X5)
% 2.69/0.98      | ~ m1_pre_topc(X0,X5)
% 2.69/0.98      | ~ m1_pre_topc(X4,X0)
% 2.69/0.98      | ~ r2_hidden(X3,X6)
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.69/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.69/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.69/0.98      | ~ v1_funct_1(X2)
% 2.69/0.98      | v2_struct_0(X5)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X4)
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | ~ l1_pre_topc(X5)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X5)
% 2.69/0.98      | ~ v2_pre_topc(X1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f103]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_15,plain,
% 2.69/0.98      ( ~ v1_tsep_1(X0,X1)
% 2.69/0.98      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.69/0.98      | ~ m1_pre_topc(X0,X1)
% 2.69/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f101]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_16,plain,
% 2.69/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.69/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/0.98      | ~ l1_pre_topc(X1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_220,plain,
% 2.69/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.69/0.98      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.69/0.98      | ~ v1_tsep_1(X0,X1)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X1) ),
% 2.69/0.98      inference(global_propositional_subsumption,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_15,c_16]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_221,plain,
% 2.69/0.98      ( ~ v1_tsep_1(X0,X1)
% 2.69/0.98      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.69/0.98      | ~ m1_pre_topc(X0,X1)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X1) ),
% 2.69/0.98      inference(renaming,[status(thm)],[c_220]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_27,negated_conjecture,
% 2.69/0.98      ( v1_tsep_1(sK3,sK4) ),
% 2.69/0.98      inference(cnf_transformation,[],[f90]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_510,plain,
% 2.69/0.98      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.69/0.98      | ~ m1_pre_topc(X0,X1)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | sK4 != X1
% 2.69/0.98      | sK3 != X0 ),
% 2.69/0.98      inference(resolution_lifted,[status(thm)],[c_221,c_27]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_511,plain,
% 2.69/0.98      ( v3_pre_topc(u1_struct_0(sK3),sK4)
% 2.69/0.98      | ~ m1_pre_topc(sK3,sK4)
% 2.69/0.98      | ~ l1_pre_topc(sK4)
% 2.69/0.98      | ~ v2_pre_topc(sK4) ),
% 2.69/0.98      inference(unflattening,[status(thm)],[c_510]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_26,negated_conjecture,
% 2.69/0.98      ( m1_pre_topc(sK3,sK4) ),
% 2.69/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_513,plain,
% 2.69/0.98      ( v3_pre_topc(u1_struct_0(sK3),sK4)
% 2.69/0.98      | ~ l1_pre_topc(sK4)
% 2.69/0.98      | ~ v2_pre_topc(sK4) ),
% 2.69/0.98      inference(global_propositional_subsumption,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_511,c_26]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_585,plain,
% 2.69/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.69/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.69/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.69/0.98      | ~ m1_pre_topc(X0,X5)
% 2.69/0.98      | ~ m1_pre_topc(X4,X0)
% 2.69/0.98      | ~ m1_pre_topc(X4,X5)
% 2.69/0.98      | ~ r2_hidden(X3,X6)
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.69/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.69/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.69/0.98      | ~ v1_funct_1(X2)
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X5)
% 2.69/0.98      | v2_struct_0(X4)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X5)
% 2.69/0.98      | ~ l1_pre_topc(sK4)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X5)
% 2.69/0.98      | ~ v2_pre_topc(sK4)
% 2.69/0.98      | u1_struct_0(sK3) != X6
% 2.69/0.98      | sK4 != X0 ),
% 2.69/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_513]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_586,plain,
% 2.69/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,X3),X4)
% 2.69/0.98      | r1_tmap_1(sK4,X1,X3,X4)
% 2.69/0.98      | ~ v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(X1))
% 2.69/0.98      | ~ m1_pre_topc(X0,X2)
% 2.69/0.98      | ~ m1_pre_topc(X0,sK4)
% 2.69/0.98      | ~ m1_pre_topc(sK4,X2)
% 2.69/0.98      | ~ r2_hidden(X4,u1_struct_0(sK3))
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 2.69/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 2.69/0.98      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.69/0.98      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 2.69/0.98      | ~ v1_funct_1(X3)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X2)
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | v2_struct_0(sK4)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X2)
% 2.69/0.98      | ~ l1_pre_topc(sK4)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X2)
% 2.69/0.98      | ~ v2_pre_topc(sK4) ),
% 2.69/0.98      inference(unflattening,[status(thm)],[c_585]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_590,plain,
% 2.69/0.98      ( v2_struct_0(X0)
% 2.69/0.98      | v2_struct_0(X2)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | ~ v1_funct_1(X3)
% 2.69/0.98      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.69/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.69/0.98      | ~ r2_hidden(X4,u1_struct_0(sK3))
% 2.69/0.98      | ~ m1_pre_topc(sK4,X2)
% 2.69/0.98      | ~ m1_pre_topc(X0,sK4)
% 2.69/0.98      | ~ m1_pre_topc(X0,X2)
% 2.69/0.98      | ~ v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(X1))
% 2.69/0.98      | r1_tmap_1(sK4,X1,X3,X4)
% 2.69/0.98      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,X3),X4)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X2)
% 2.69/0.98      | ~ l1_pre_topc(sK4)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X2)
% 2.69/0.98      | ~ v2_pre_topc(sK4) ),
% 2.69/0.98      inference(global_propositional_subsumption,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_586,c_32]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_591,plain,
% 2.69/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,X3),X4)
% 2.69/0.98      | r1_tmap_1(sK4,X1,X3,X4)
% 2.69/0.98      | ~ v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(X1))
% 2.69/0.98      | ~ m1_pre_topc(X0,X2)
% 2.69/0.98      | ~ m1_pre_topc(X0,sK4)
% 2.69/0.98      | ~ m1_pre_topc(sK4,X2)
% 2.69/0.98      | ~ r2_hidden(X4,u1_struct_0(sK3))
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 2.69/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 2.69/0.98      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.69/0.98      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 2.69/0.98      | ~ v1_funct_1(X3)
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X2)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X2)
% 2.69/0.98      | ~ l1_pre_topc(sK4)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X2)
% 2.69/0.98      | ~ v2_pre_topc(sK4) ),
% 2.69/0.98      inference(renaming,[status(thm)],[c_590]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_9,plain,
% 2.69/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.69/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_640,plain,
% 2.69/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,X3),X4)
% 2.69/0.98      | r1_tmap_1(sK4,X1,X3,X4)
% 2.69/0.98      | ~ v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(X1))
% 2.69/0.98      | ~ m1_pre_topc(X0,sK4)
% 2.69/0.98      | ~ m1_pre_topc(sK4,X2)
% 2.69/0.98      | ~ r2_hidden(X4,u1_struct_0(sK3))
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 2.69/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 2.69/0.98      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.69/0.98      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 2.69/0.98      | ~ v1_funct_1(X3)
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X2)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X2)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X2) ),
% 2.69/0.98      inference(forward_subsumption_resolution,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_591,c_8,c_9,c_17]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_788,plain,
% 2.69/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,X3),X4)
% 2.69/0.98      | r1_tmap_1(sK4,X1,X3,X4)
% 2.69/0.98      | ~ m1_pre_topc(X0,sK4)
% 2.69/0.98      | ~ m1_pre_topc(sK4,X2)
% 2.69/0.98      | ~ r2_hidden(X4,u1_struct_0(sK3))
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(X4,u1_struct_0(sK4))
% 2.69/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 2.69/0.98      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.69/0.98      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 2.69/0.98      | ~ v1_funct_1(X3)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | v2_struct_0(X2)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X2)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X2)
% 2.69/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.69/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.69/0.98      | sK5 != X3 ),
% 2.69/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_640]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_789,plain,
% 2.69/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
% 2.69/0.98      | r1_tmap_1(sK4,X1,sK5,X3)
% 2.69/0.98      | ~ m1_pre_topc(X0,sK4)
% 2.69/0.98      | ~ m1_pre_topc(sK4,X2)
% 2.69/0.98      | ~ r2_hidden(X3,u1_struct_0(sK3))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 2.69/0.98      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.69/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 2.69/0.98      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 2.69/0.98      | ~ v1_funct_1(sK5)
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X2)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X2)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X2)
% 2.69/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.69/0.98      inference(unflattening,[status(thm)],[c_788]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_793,plain,
% 2.69/0.98      ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 2.69/0.98      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.69/0.98      | ~ r2_hidden(X3,u1_struct_0(sK3))
% 2.69/0.98      | ~ m1_pre_topc(sK4,X2)
% 2.69/0.98      | ~ m1_pre_topc(X0,sK4)
% 2.69/0.98      | r1_tmap_1(sK4,X1,sK5,X3)
% 2.69/0.98      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X2)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X2)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X2)
% 2.69/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.69/0.98      inference(global_propositional_subsumption,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_789,c_30]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_794,plain,
% 2.69/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
% 2.69/0.98      | r1_tmap_1(sK4,X1,sK5,X3)
% 2.69/0.98      | ~ m1_pre_topc(X0,sK4)
% 2.69/0.98      | ~ m1_pre_topc(sK4,X2)
% 2.69/0.98      | ~ r2_hidden(X3,u1_struct_0(sK3))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.69/0.98      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 2.69/0.98      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.69/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 2.69/0.98      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 2.69/0.98      | v2_struct_0(X0)
% 2.69/0.98      | v2_struct_0(X1)
% 2.69/0.98      | v2_struct_0(X2)
% 2.69/0.98      | ~ l1_pre_topc(X1)
% 2.69/0.98      | ~ l1_pre_topc(X2)
% 2.69/0.98      | ~ v2_pre_topc(X1)
% 2.69/0.98      | ~ v2_pre_topc(X2)
% 2.69/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.69/0.98      inference(renaming,[status(thm)],[c_793]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2294,plain,
% 2.69/0.98      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 2.69/0.98      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 2.69/0.98      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 2.69/0.98      | m1_pre_topc(X1,sK4) != iProver_top
% 2.69/0.98      | m1_pre_topc(sK4,X2) != iProver_top
% 2.69/0.98      | r2_hidden(X3,u1_struct_0(sK3)) != iProver_top
% 2.69/0.98      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.69/0.98      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.69/0.98      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.69/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.69/0.98      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1)) != iProver_top
% 2.69/0.98      | v2_struct_0(X0) = iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | v2_struct_0(X2) = iProver_top
% 2.69/0.98      | l1_pre_topc(X0) != iProver_top
% 2.69/0.98      | l1_pre_topc(X2) != iProver_top
% 2.69/0.98      | v2_pre_topc(X0) != iProver_top
% 2.69/0.98      | v2_pre_topc(X2) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2759,plain,
% 2.69/0.98      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.69/0.98      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.69/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.69/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 2.69/0.98      | r2_hidden(X2,u1_struct_0(sK3)) != iProver_top
% 2.69/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.69/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.69/0.98      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.69/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.69/0.98      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | v2_struct_0(X0) = iProver_top
% 2.69/0.98      | v2_struct_0(sK2) = iProver_top
% 2.69/0.98      | l1_pre_topc(X1) != iProver_top
% 2.69/0.98      | l1_pre_topc(sK2) != iProver_top
% 2.69/0.98      | v2_pre_topc(X1) != iProver_top
% 2.69/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 2.69/0.98      inference(equality_resolution,[status(thm)],[c_2294]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_38,negated_conjecture,
% 2.69/0.98      ( l1_pre_topc(sK1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_43,plain,
% 2.69/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_31,negated_conjecture,
% 2.69/0.98      ( m1_pre_topc(sK4,sK1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_50,plain,
% 2.69/0.98      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_55,plain,
% 2.69/0.98      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2622,plain,
% 2.69/0.98      ( ~ m1_pre_topc(sK3,sK4)
% 2.69/0.98      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.69/0.98      | ~ l1_pre_topc(sK4) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2623,plain,
% 2.69/0.98      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.69/0.98      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.69/0.98      | l1_pre_topc(sK4) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_2622]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2765,plain,
% 2.69/0.98      ( ~ m1_pre_topc(sK4,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK4) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3019,plain,
% 2.69/0.98      ( ~ m1_pre_topc(sK4,sK1) | l1_pre_topc(sK4) | ~ l1_pre_topc(sK1) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_2765]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3020,plain,
% 2.69/0.98      ( m1_pre_topc(sK4,sK1) != iProver_top
% 2.69/0.98      | l1_pre_topc(sK4) = iProver_top
% 2.69/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_3019]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3103,plain,
% 2.69/0.98      ( v2_pre_topc(X1) != iProver_top
% 2.69/0.98      | v2_struct_0(X0) = iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 2.69/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.69/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.69/0.98      | r2_hidden(X2,u1_struct_0(sK3)) != iProver_top
% 2.69/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 2.69/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.69/0.98      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.69/0.98      | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.69/0.98      | l1_pre_topc(X1) != iProver_top ),
% 2.69/0.98      inference(global_propositional_subsumption,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_2759,c_43,c_44,c_45,c_46,c_50,c_53,c_55,c_2623,c_3020]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3104,plain,
% 2.69/0.98      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.69/0.98      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.69/0.98      | m1_pre_topc(X0,sK4) != iProver_top
% 2.69/0.98      | m1_pre_topc(sK4,X1) != iProver_top
% 2.69/0.98      | r2_hidden(X2,u1_struct_0(sK3)) != iProver_top
% 2.69/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.69/0.98      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.69/0.98      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 2.69/0.98      | v2_struct_0(X1) = iProver_top
% 2.69/0.98      | v2_struct_0(X0) = iProver_top
% 2.69/0.98      | l1_pre_topc(X1) != iProver_top
% 2.69/0.98      | v2_pre_topc(X1) != iProver_top ),
% 2.69/0.98      inference(renaming,[status(thm)],[c_3103]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3121,plain,
% 2.69/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
% 2.69/0.98      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.69/0.98      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.69/0.98      | r2_hidden(sK7,u1_struct_0(sK3)) != iProver_top
% 2.69/0.98      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 2.69/0.98      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.69/0.98      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 2.69/0.98      | v2_struct_0(sK1) = iProver_top
% 2.69/0.98      | v2_struct_0(sK3) = iProver_top
% 2.69/0.98      | l1_pre_topc(sK1) != iProver_top
% 2.69/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_2394,c_3104]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_40,negated_conjecture,
% 2.69/0.98      ( ~ v2_struct_0(sK1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_41,plain,
% 2.69/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_39,negated_conjecture,
% 2.69/0.98      ( v2_pre_topc(sK1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_42,plain,
% 2.69/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_34,negated_conjecture,
% 2.69/0.98      ( ~ v2_struct_0(sK3) ),
% 2.69/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_47,plain,
% 2.69/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_57,plain,
% 2.69/0.98      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_25,negated_conjecture,
% 2.69/0.98      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.69/0.98      inference(cnf_transformation,[],[f92]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2310,plain,
% 2.69/0.98      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2351,plain,
% 2.69/0.98      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 2.69/0.98      inference(light_normalisation,[status(thm)],[c_2310,c_23]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1,plain,
% 2.69/0.98      ( r1_tarski(X0,X0) ),
% 2.69/0.98      inference(cnf_transformation,[],[f97]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3559,plain,
% 2.69/0.98      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3560,plain,
% 2.69/0.98      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_3559]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3585,plain,
% 2.69/0.98      ( r2_hidden(sK7,u1_struct_0(sK3)) != iProver_top
% 2.69/0.98      | r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top ),
% 2.69/0.98      inference(global_propositional_subsumption,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_3121,c_41,c_42,c_43,c_47,c_50,c_55,c_57,c_2351,c_3560]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3586,plain,
% 2.69/0.98      ( r1_tmap_1(sK4,sK2,sK5,sK7) = iProver_top
% 2.69/0.98      | r2_hidden(sK7,u1_struct_0(sK3)) != iProver_top ),
% 2.69/0.98      inference(renaming,[status(thm)],[c_3585]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_6,plain,
% 2.69/0.98      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2319,plain,
% 2.69/0.98      ( r2_hidden(X0,X1) = iProver_top
% 2.69/0.98      | m1_subset_1(X0,X1) != iProver_top
% 2.69/0.98      | v1_xboole_0(X1) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3256,plain,
% 2.69/0.98      ( r2_hidden(sK7,u1_struct_0(sK3)) = iProver_top
% 2.69/0.98      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_2311,c_2319]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2309,plain,
% 2.69/0.98      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2316,plain,
% 2.69/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 2.69/0.98      | l1_pre_topc(X1) != iProver_top
% 2.69/0.98      | l1_pre_topc(X0) = iProver_top ),
% 2.69/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3234,plain,
% 2.69/0.98      ( l1_pre_topc(sK4) != iProver_top
% 2.69/0.98      | l1_pre_topc(sK3) = iProver_top ),
% 2.69/0.98      inference(superposition,[status(thm)],[c_2309,c_2316]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(contradiction,plain,
% 2.69/0.98      ( $false ),
% 2.69/0.98      inference(minisat,
% 2.69/0.98                [status(thm)],
% 2.69/0.98                [c_5140,c_4292,c_4058,c_3750,c_3586,c_3256,c_3234,c_3020,
% 2.69/0.98                 c_2351,c_57,c_55,c_50,c_47,c_43,c_42,c_41]) ).
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/0.98  
% 2.69/0.98  ------                               Statistics
% 2.69/0.98  
% 2.69/0.98  ------ General
% 2.69/0.98  
% 2.69/0.98  abstr_ref_over_cycles:                  0
% 2.69/0.98  abstr_ref_under_cycles:                 0
% 2.69/0.98  gc_basic_clause_elim:                   0
% 2.69/0.98  forced_gc_time:                         0
% 2.69/0.98  parsing_time:                           0.014
% 2.69/0.98  unif_index_cands_time:                  0.
% 2.69/0.98  unif_index_add_time:                    0.
% 2.69/0.98  orderings_time:                         0.
% 2.69/0.98  out_proof_time:                         0.023
% 2.69/0.98  total_time:                             0.239
% 2.69/0.98  num_of_symbols:                         57
% 2.69/0.98  num_of_terms:                           2860
% 2.69/0.98  
% 2.69/0.98  ------ Preprocessing
% 2.69/0.98  
% 2.69/0.98  num_of_splits:                          0
% 2.69/0.98  num_of_split_atoms:                     0
% 2.69/0.98  num_of_reused_defs:                     0
% 2.69/0.98  num_eq_ax_congr_red:                    17
% 2.69/0.98  num_of_sem_filtered_clauses:            1
% 2.69/0.98  num_of_subtypes:                        0
% 2.69/0.98  monotx_restored_types:                  0
% 2.69/0.98  sat_num_of_epr_types:                   0
% 2.69/0.98  sat_num_of_non_cyclic_types:            0
% 2.69/0.98  sat_guarded_non_collapsed_types:        0
% 2.69/0.98  num_pure_diseq_elim:                    0
% 2.69/0.98  simp_replaced_by:                       0
% 2.69/0.98  res_preprocessed:                       164
% 2.69/0.98  prep_upred:                             0
% 2.69/0.98  prep_unflattend:                        27
% 2.69/0.98  smt_new_axioms:                         0
% 2.69/0.98  pred_elim_cands:                        9
% 2.69/0.98  pred_elim:                              5
% 2.69/0.98  pred_elim_cl:                           7
% 2.69/0.98  pred_elim_cycles:                       7
% 2.69/0.98  merged_defs:                            8
% 2.69/0.98  merged_defs_ncl:                        0
% 2.69/0.98  bin_hyper_res:                          8
% 2.69/0.98  prep_cycles:                            4
% 2.69/0.98  pred_elim_time:                         0.028
% 2.69/0.98  splitting_time:                         0.
% 2.69/0.98  sem_filter_time:                        0.
% 2.69/0.98  monotx_time:                            0.001
% 2.69/0.98  subtype_inf_time:                       0.
% 2.69/0.98  
% 2.69/0.98  ------ Problem properties
% 2.69/0.98  
% 2.69/0.98  clauses:                                32
% 2.69/0.98  conjectures:                            17
% 2.69/0.98  epr:                                    21
% 2.69/0.98  horn:                                   25
% 2.69/0.98  ground:                                 17
% 2.69/0.98  unary:                                  16
% 2.69/0.98  binary:                                 2
% 2.69/0.98  lits:                                   98
% 2.69/0.98  lits_eq:                                5
% 2.69/0.98  fd_pure:                                0
% 2.69/0.98  fd_pseudo:                              0
% 2.69/0.98  fd_cond:                                0
% 2.69/0.98  fd_pseudo_cond:                         1
% 2.69/0.98  ac_symbols:                             0
% 2.69/0.98  
% 2.69/0.98  ------ Propositional Solver
% 2.69/0.98  
% 2.69/0.98  prop_solver_calls:                      27
% 2.69/0.98  prop_fast_solver_calls:                 1717
% 2.69/0.98  smt_solver_calls:                       0
% 2.69/0.98  smt_fast_solver_calls:                  0
% 2.69/0.98  prop_num_of_clauses:                    1307
% 2.69/0.98  prop_preprocess_simplified:             5217
% 2.69/0.98  prop_fo_subsumed:                       62
% 2.69/0.98  prop_solver_time:                       0.
% 2.69/0.98  smt_solver_time:                        0.
% 2.69/0.98  smt_fast_solver_time:                   0.
% 2.69/0.98  prop_fast_solver_time:                  0.
% 2.69/0.98  prop_unsat_core_time:                   0.
% 2.69/0.98  
% 2.69/0.98  ------ QBF
% 2.69/0.98  
% 2.69/0.98  qbf_q_res:                              0
% 2.69/0.98  qbf_num_tautologies:                    0
% 2.69/0.98  qbf_prep_cycles:                        0
% 2.69/0.98  
% 2.69/0.98  ------ BMC1
% 2.69/0.98  
% 2.69/0.98  bmc1_current_bound:                     -1
% 2.69/0.98  bmc1_last_solved_bound:                 -1
% 2.69/0.98  bmc1_unsat_core_size:                   -1
% 2.69/0.98  bmc1_unsat_core_parents_size:           -1
% 2.69/0.98  bmc1_merge_next_fun:                    0
% 2.69/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.69/0.98  
% 2.69/0.98  ------ Instantiation
% 2.69/0.98  
% 2.69/0.98  inst_num_of_clauses:                    383
% 2.69/0.98  inst_num_in_passive:                    67
% 2.69/0.98  inst_num_in_active:                     291
% 2.69/0.98  inst_num_in_unprocessed:                25
% 2.69/0.98  inst_num_of_loops:                      340
% 2.69/0.98  inst_num_of_learning_restarts:          0
% 2.69/0.98  inst_num_moves_active_passive:          45
% 2.69/0.98  inst_lit_activity:                      0
% 2.69/0.98  inst_lit_activity_moves:                0
% 2.69/0.98  inst_num_tautologies:                   0
% 2.69/0.98  inst_num_prop_implied:                  0
% 2.69/0.98  inst_num_existing_simplified:           0
% 2.69/0.98  inst_num_eq_res_simplified:             0
% 2.69/0.98  inst_num_child_elim:                    0
% 2.69/0.98  inst_num_of_dismatching_blockings:      20
% 2.69/0.98  inst_num_of_non_proper_insts:           491
% 2.69/0.98  inst_num_of_duplicates:                 0
% 2.69/0.98  inst_inst_num_from_inst_to_res:         0
% 2.69/0.98  inst_dismatching_checking_time:         0.
% 2.69/0.98  
% 2.69/0.98  ------ Resolution
% 2.69/0.98  
% 2.69/0.98  res_num_of_clauses:                     0
% 2.69/0.98  res_num_in_passive:                     0
% 2.69/0.98  res_num_in_active:                      0
% 2.69/0.98  res_num_of_loops:                       168
% 2.69/0.98  res_forward_subset_subsumed:            79
% 2.69/0.98  res_backward_subset_subsumed:           0
% 2.69/0.98  res_forward_subsumed:                   0
% 2.69/0.98  res_backward_subsumed:                  0
% 2.69/0.98  res_forward_subsumption_resolution:     4
% 2.69/0.98  res_backward_subsumption_resolution:    0
% 2.69/0.98  res_clause_to_clause_subsumption:       226
% 2.69/0.98  res_orphan_elimination:                 0
% 2.69/0.98  res_tautology_del:                      87
% 2.69/0.98  res_num_eq_res_simplified:              0
% 2.69/0.98  res_num_sel_changes:                    0
% 2.69/0.98  res_moves_from_active_to_pass:          0
% 2.69/0.98  
% 2.69/0.98  ------ Superposition
% 2.69/0.98  
% 2.69/0.98  sup_time_total:                         0.
% 2.69/0.98  sup_time_generating:                    0.
% 2.69/0.98  sup_time_sim_full:                      0.
% 2.69/0.98  sup_time_sim_immed:                     0.
% 2.69/0.98  
% 2.69/0.98  sup_num_of_clauses:                     71
% 2.69/0.98  sup_num_in_active:                      66
% 2.69/0.98  sup_num_in_passive:                     5
% 2.69/0.98  sup_num_of_loops:                       66
% 2.69/0.98  sup_fw_superposition:                   39
% 2.69/0.98  sup_bw_superposition:                   19
% 2.69/0.98  sup_immediate_simplified:               7
% 2.69/0.98  sup_given_eliminated:                   0
% 2.69/0.98  comparisons_done:                       0
% 2.69/0.98  comparisons_avoided:                    0
% 2.69/0.98  
% 2.69/0.98  ------ Simplifications
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  sim_fw_subset_subsumed:                 7
% 2.69/0.98  sim_bw_subset_subsumed:                 2
% 2.69/0.98  sim_fw_subsumed:                        0
% 2.69/0.98  sim_bw_subsumed:                        0
% 2.69/0.98  sim_fw_subsumption_res:                 0
% 2.69/0.98  sim_bw_subsumption_res:                 0
% 2.69/0.98  sim_tautology_del:                      10
% 2.69/0.98  sim_eq_tautology_del:                   1
% 2.69/0.98  sim_eq_res_simp:                        0
% 2.69/0.98  sim_fw_demodulated:                     0
% 2.69/0.98  sim_bw_demodulated:                     0
% 2.69/0.98  sim_light_normalised:                   3
% 2.69/0.98  sim_joinable_taut:                      0
% 2.69/0.98  sim_joinable_simp:                      0
% 2.69/0.98  sim_ac_normalised:                      0
% 2.69/0.98  sim_smt_subsumption:                    0
% 2.69/0.98  
%------------------------------------------------------------------------------
