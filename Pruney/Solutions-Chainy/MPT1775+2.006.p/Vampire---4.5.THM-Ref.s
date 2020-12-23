%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:55 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :  163 (1129 expanded)
%              Number of leaves         :   22 ( 530 expanded)
%              Depth                    :   32
%              Number of atoms          : 1338 (22311 expanded)
%              Number of equality atoms :   40 (1341 expanded)
%              Maximal formula depth    :   32 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f101,f133,f239,f276,f288])).

fof(f288,plain,(
    ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f286,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f34,f41,f40,f39,f38,f37,f36,f35])).

fof(f35,plain,
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

fof(f36,plain,
    ( ? [X1] :
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
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,sK1,X4,X5) )
                          & ( r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                            | r1_tmap_1(X3,sK1,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & v1_tsep_1(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                          | ~ r1_tmap_1(X3,sK1,X4,X5) )
                        & ( r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                          | r1_tmap_1(X3,sK1,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & v1_tsep_1(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                        | ~ r1_tmap_1(X3,sK1,X4,X5) )
                      & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                        | r1_tmap_1(X3,sK1,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK2,X3)
              & v1_tsep_1(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                      | ~ r1_tmap_1(X3,sK1,X4,X5) )
                    & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                      | r1_tmap_1(X3,sK1,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK2)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK2,X3)
            & v1_tsep_1(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                    | ~ r1_tmap_1(sK3,sK1,X4,X5) )
                  & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                    | r1_tmap_1(sK3,sK1,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK2)) )
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & m1_pre_topc(sK2,sK3)
          & v1_tsep_1(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                  | ~ r1_tmap_1(sK3,sK1,X4,X5) )
                & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                  | r1_tmap_1(sK3,sK1,X4,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK2)) )
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & m1_pre_topc(sK2,sK3)
        & v1_tsep_1(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
                | ~ r1_tmap_1(sK3,sK1,sK4,X5) )
              & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
                | r1_tmap_1(sK3,sK1,sK4,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK2)) )
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & m1_pre_topc(sK2,sK3)
      & v1_tsep_1(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
              | ~ r1_tmap_1(sK3,sK1,sK4,X5) )
            & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
              | r1_tmap_1(sK3,sK1,sK4,X5) )
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK2)) )
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ? [X6] :
          ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
            | ~ r1_tmap_1(sK3,sK1,sK4,sK5) )
          & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
            | r1_tmap_1(sK3,sK1,sK4,sK5) )
          & sK5 = X6
          & m1_subset_1(X6,u1_struct_0(sK2)) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X6] :
        ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
          | ~ r1_tmap_1(sK3,sK1,sK4,sK5) )
        & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
          | r1_tmap_1(sK3,sK1,sK4,sK5) )
        & sK5 = X6
        & m1_subset_1(X6,u1_struct_0(sK2)) )
   => ( ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
        | ~ r1_tmap_1(sK3,sK1,sK4,sK5) )
      & ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
        | r1_tmap_1(sK3,sK1,sK4,sK5) )
      & sK5 = sK6
      & m1_subset_1(sK6,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f286,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f285,f206])).

fof(f206,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f111,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f111,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f108,f50])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f108,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f69,f55])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f285,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_6 ),
    inference(resolution,[],[f132,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f132,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl7_6
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f276,plain,
    ( ~ spl7_1
    | spl7_2
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f274,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f274,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f273,f49])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f273,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f272,f50])).

fof(f272,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f271,f240])).

fof(f240,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | spl7_2 ),
    inference(forward_demodulation,[],[f99,f65])).

fof(f65,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f42])).

fof(f99,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl7_2
  <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f271,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(resolution,[],[f260,f57])).

fof(f57,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f259,f54])).

fof(f259,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f258,f62])).

fof(f62,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f258,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f257,f102])).

fof(f102,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f64,f65])).

fof(f64,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f256,f164])).

fof(f164,plain,(
    v3_pre_topc(u1_struct_0(sK2),sK3) ),
    inference(subsumption_resolution,[],[f163,f149])).

fof(f149,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f148,f49])).

fof(f148,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f144,f50])).

fof(f144,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f74,f57])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f163,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f162,f112])).

fof(f112,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f109,f50])).

fof(f109,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f69,f57])).

fof(f162,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f161,f62])).

fof(f161,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f104,f61])).

fof(f61,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f91,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

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
    inference(nnf_transformation,[],[f28])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f256,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(u1_struct_0(sK2),sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f255,f128])).

fof(f128,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_5
  <=> r2_hidden(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,u1_struct_0(sK2))
        | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl7_1 ),
    inference(resolution,[],[f251,f157])).

fof(f157,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f154,f112])).

fof(f154,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f70,f62])).

fof(f251,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(sK5,u1_struct_0(X0))
        | ~ v3_pre_topc(u1_struct_0(X0),sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_1 ),
    inference(resolution,[],[f250,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,u1_struct_0(X0))
        | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ r2_hidden(sK5,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f249,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f249,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ r2_hidden(sK5,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f248,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f248,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ r2_hidden(sK5,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f247,f52])).

fof(f52,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f247,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ r2_hidden(sK5,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f246,f53])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f246,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ r2_hidden(sK5,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f245,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f245,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ r2_hidden(sK5,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f244,f58])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f244,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ r2_hidden(sK5,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f243,f59])).

fof(f59,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f243,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ r2_hidden(sK5,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f242,f60])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f242,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ r2_hidden(sK5,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f241,f63])).

fof(f63,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f241,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ r2_hidden(sK5,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_1 ),
    inference(resolution,[],[f94,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r1_tmap_1(X3,X1,X4,X7)
      | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
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
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f94,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_1
  <=> r1_tmap_1(sK3,sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f239,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f237,f89])).

fof(f237,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f236,f164])).

fof(f236,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f235,f128])).

fof(f235,plain,
    ( ~ r2_hidden(sK5,u1_struct_0(sK2))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2))
    | spl7_1
    | ~ spl7_2 ),
    inference(resolution,[],[f182,f157])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ r1_tarski(X0,u1_struct_0(sK2)) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f181,f48])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f180,f49])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f179,f50])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f178,f51])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f177,f52])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f176,f53])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f175,f54])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f174,f55])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f173,f56])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f172,f57])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f171,f58])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f170,f59])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f169,f60])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f168,f62])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f167,f63])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f166,f102])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f165,f95])).

fof(f95,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f165,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK3,sK1,sK4,sK5)
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK5,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f84,f105])).

fof(f105,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f98,f65])).

fof(f98,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f84,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7)
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
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f133,plain,
    ( spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f114,f130,f126])).

fof(f114,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[],[f79,f102])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f101,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f66,f97,f93])).

fof(f66,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f100,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f67,f97,f93])).

fof(f67,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:27:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (785186816)
% 0.14/0.37  ipcrm: permission denied for id (786497537)
% 0.14/0.37  ipcrm: permission denied for id (786595844)
% 0.14/0.37  ipcrm: permission denied for id (785219590)
% 0.14/0.38  ipcrm: permission denied for id (785252359)
% 0.14/0.38  ipcrm: permission denied for id (786661384)
% 0.14/0.38  ipcrm: permission denied for id (786694153)
% 0.14/0.38  ipcrm: permission denied for id (786726922)
% 0.14/0.38  ipcrm: permission denied for id (786759691)
% 0.14/0.38  ipcrm: permission denied for id (785317901)
% 0.14/0.39  ipcrm: permission denied for id (786923537)
% 0.14/0.39  ipcrm: permission denied for id (786989075)
% 0.14/0.39  ipcrm: permission denied for id (787054613)
% 0.14/0.39  ipcrm: permission denied for id (785416214)
% 0.14/0.40  ipcrm: permission denied for id (785448984)
% 0.14/0.40  ipcrm: permission denied for id (787120153)
% 0.14/0.40  ipcrm: permission denied for id (787218460)
% 0.14/0.40  ipcrm: permission denied for id (787283998)
% 0.14/0.41  ipcrm: permission denied for id (787316767)
% 0.14/0.41  ipcrm: permission denied for id (785580064)
% 0.21/0.41  ipcrm: permission denied for id (785612833)
% 0.21/0.41  ipcrm: permission denied for id (787349538)
% 0.21/0.41  ipcrm: permission denied for id (787415076)
% 0.21/0.41  ipcrm: permission denied for id (787480614)
% 0.21/0.42  ipcrm: permission denied for id (787546152)
% 0.21/0.42  ipcrm: permission denied for id (787611689)
% 0.21/0.42  ipcrm: permission denied for id (787644458)
% 0.21/0.42  ipcrm: permission denied for id (785678379)
% 0.21/0.42  ipcrm: permission denied for id (787677228)
% 0.21/0.42  ipcrm: permission denied for id (785711150)
% 0.21/0.43  ipcrm: permission denied for id (785743919)
% 0.21/0.43  ipcrm: permission denied for id (787742768)
% 0.21/0.43  ipcrm: permission denied for id (787808306)
% 0.21/0.44  ipcrm: permission denied for id (785809463)
% 0.21/0.44  ipcrm: permission denied for id (788070457)
% 0.21/0.44  ipcrm: permission denied for id (788168764)
% 0.21/0.44  ipcrm: permission denied for id (788234302)
% 0.21/0.45  ipcrm: permission denied for id (788430916)
% 0.21/0.45  ipcrm: permission denied for id (788496454)
% 0.21/0.46  ipcrm: permission denied for id (785940551)
% 0.21/0.46  ipcrm: permission denied for id (785973321)
% 0.21/0.46  ipcrm: permission denied for id (788561994)
% 0.21/0.46  ipcrm: permission denied for id (788594763)
% 0.21/0.46  ipcrm: permission denied for id (788627532)
% 0.21/0.46  ipcrm: permission denied for id (786006093)
% 0.21/0.47  ipcrm: permission denied for id (788693071)
% 0.21/0.47  ipcrm: permission denied for id (786038864)
% 0.21/0.47  ipcrm: permission denied for id (788725841)
% 0.21/0.47  ipcrm: permission denied for id (786071634)
% 0.21/0.47  ipcrm: permission denied for id (788758611)
% 0.21/0.47  ipcrm: permission denied for id (788856918)
% 0.21/0.48  ipcrm: permission denied for id (788889687)
% 0.21/0.48  ipcrm: permission denied for id (786104409)
% 0.21/0.48  ipcrm: permission denied for id (789053532)
% 0.21/0.48  ipcrm: permission denied for id (789086301)
% 0.21/0.48  ipcrm: permission denied for id (786137182)
% 0.21/0.49  ipcrm: permission denied for id (789119071)
% 0.21/0.49  ipcrm: permission denied for id (789151840)
% 0.21/0.49  ipcrm: permission denied for id (789217378)
% 0.21/0.49  ipcrm: permission denied for id (789282916)
% 0.21/0.49  ipcrm: permission denied for id (789315685)
% 0.21/0.49  ipcrm: permission denied for id (786169958)
% 0.21/0.50  ipcrm: permission denied for id (789381224)
% 0.21/0.50  ipcrm: permission denied for id (789413993)
% 0.21/0.50  ipcrm: permission denied for id (789446762)
% 0.21/0.50  ipcrm: permission denied for id (789479531)
% 0.21/0.51  ipcrm: permission denied for id (789643376)
% 0.21/0.51  ipcrm: permission denied for id (789708913)
% 0.21/0.51  ipcrm: permission denied for id (786333810)
% 0.21/0.51  ipcrm: permission denied for id (789741683)
% 0.21/0.51  ipcrm: permission denied for id (789807221)
% 0.21/0.51  ipcrm: permission denied for id (789839990)
% 0.21/0.52  ipcrm: permission denied for id (786399353)
% 0.21/0.52  ipcrm: permission denied for id (789971067)
% 0.21/0.52  ipcrm: permission denied for id (790003836)
% 0.21/0.52  ipcrm: permission denied for id (790036605)
% 0.21/0.53  ipcrm: permission denied for id (786464895)
% 1.13/0.65  % (4870)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.13/0.66  % (4878)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.13/0.66  % (4863)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.13/0.66  % (4872)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.13/0.66  % (4869)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.13/0.67  % (4877)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.13/0.67  % (4860)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.13/0.67  % (4860)Refutation not found, incomplete strategy% (4860)------------------------------
% 1.13/0.67  % (4860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.67  % (4862)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.13/0.67  % (4865)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.13/0.67  % (4864)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.13/0.67  % (4870)Refutation found. Thanks to Tanya!
% 1.13/0.67  % SZS status Theorem for theBenchmark
% 1.13/0.67  % SZS output start Proof for theBenchmark
% 1.13/0.67  fof(f289,plain,(
% 1.13/0.67    $false),
% 1.13/0.67    inference(avatar_sat_refutation,[],[f100,f101,f133,f239,f276,f288])).
% 1.13/0.67  fof(f288,plain,(
% 1.13/0.67    ~spl7_6),
% 1.13/0.67    inference(avatar_contradiction_clause,[],[f287])).
% 1.13/0.67  fof(f287,plain,(
% 1.13/0.67    $false | ~spl7_6),
% 1.13/0.67    inference(subsumption_resolution,[],[f286,f54])).
% 1.13/0.67  fof(f54,plain,(
% 1.13/0.67    ~v2_struct_0(sK2)),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f42,plain,(
% 1.13/0.67    (((((((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.13/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f34,f41,f40,f39,f38,f37,f36,f35])).
% 1.13/0.67  fof(f35,plain,(
% 1.13/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.13/0.67    introduced(choice_axiom,[])).
% 1.13/0.67  fof(f36,plain,(
% 1.13/0.67    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.13/0.67    introduced(choice_axiom,[])).
% 1.13/0.67  fof(f37,plain,(
% 1.13/0.67    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & v1_tsep_1(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.13/0.67    introduced(choice_axiom,[])).
% 1.13/0.67  fof(f38,plain,(
% 1.13/0.67    ? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & v1_tsep_1(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | ~r1_tmap_1(sK3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | r1_tmap_1(sK3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.13/0.67    introduced(choice_axiom,[])).
% 1.13/0.67  fof(f39,plain,(
% 1.13/0.67    ? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | ~r1_tmap_1(sK3,sK1,X4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) | r1_tmap_1(sK3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & v1_tsep_1(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 1.13/0.67    introduced(choice_axiom,[])).
% 1.13/0.67  fof(f40,plain,(
% 1.13/0.67    ? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,X5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 1.13/0.67    introduced(choice_axiom,[])).
% 1.13/0.67  fof(f41,plain,(
% 1.13/0.67    ? [X6] : ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => ((~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)) & (r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 1.13/0.67    introduced(choice_axiom,[])).
% 1.13/0.67  fof(f34,plain,(
% 1.13/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.13/0.67    inference(flattening,[],[f33])).
% 1.13/0.67  fof(f33,plain,(
% 1.13/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.13/0.67    inference(nnf_transformation,[],[f15])).
% 1.13/0.67  fof(f15,plain,(
% 1.13/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.13/0.67    inference(flattening,[],[f14])).
% 1.13/0.67  fof(f14,plain,(
% 1.13/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.13/0.67    inference(ennf_transformation,[],[f13])).
% 1.13/0.67  fof(f13,negated_conjecture,(
% 1.13/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.13/0.67    inference(negated_conjecture,[],[f12])).
% 1.13/0.67  fof(f12,conjecture,(
% 1.13/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).
% 1.13/0.67  fof(f286,plain,(
% 1.13/0.67    v2_struct_0(sK2) | ~spl7_6),
% 1.13/0.67    inference(subsumption_resolution,[],[f285,f206])).
% 1.13/0.67  fof(f206,plain,(
% 1.13/0.67    l1_struct_0(sK2)),
% 1.13/0.67    inference(resolution,[],[f111,f68])).
% 1.13/0.67  fof(f68,plain,(
% 1.13/0.67    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.13/0.67    inference(cnf_transformation,[],[f16])).
% 1.13/0.67  fof(f16,plain,(
% 1.13/0.67    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.13/0.67    inference(ennf_transformation,[],[f5])).
% 1.13/0.67  fof(f5,axiom,(
% 1.13/0.67    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.13/0.67  fof(f111,plain,(
% 1.13/0.67    l1_pre_topc(sK2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f108,f50])).
% 1.13/0.67  fof(f50,plain,(
% 1.13/0.67    l1_pre_topc(sK0)),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f108,plain,(
% 1.13/0.67    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 1.13/0.67    inference(resolution,[],[f69,f55])).
% 1.13/0.67  fof(f55,plain,(
% 1.13/0.67    m1_pre_topc(sK2,sK0)),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f69,plain,(
% 1.13/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.13/0.67    inference(cnf_transformation,[],[f17])).
% 1.13/0.67  fof(f17,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.13/0.67    inference(ennf_transformation,[],[f6])).
% 1.13/0.67  fof(f6,axiom,(
% 1.13/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.13/0.67  fof(f285,plain,(
% 1.13/0.67    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl7_6),
% 1.13/0.67    inference(resolution,[],[f132,f71])).
% 1.13/0.67  fof(f71,plain,(
% 1.13/0.67    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.13/0.67    inference(cnf_transformation,[],[f20])).
% 1.13/0.67  fof(f20,plain,(
% 1.13/0.67    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.13/0.67    inference(flattening,[],[f19])).
% 1.13/0.67  fof(f19,plain,(
% 1.13/0.67    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.13/0.67    inference(ennf_transformation,[],[f7])).
% 1.13/0.67  fof(f7,axiom,(
% 1.13/0.67    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.13/0.67  fof(f132,plain,(
% 1.13/0.67    v1_xboole_0(u1_struct_0(sK2)) | ~spl7_6),
% 1.13/0.67    inference(avatar_component_clause,[],[f130])).
% 1.13/0.67  fof(f130,plain,(
% 1.13/0.67    spl7_6 <=> v1_xboole_0(u1_struct_0(sK2))),
% 1.13/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.13/0.67  fof(f276,plain,(
% 1.13/0.67    ~spl7_1 | spl7_2 | ~spl7_5),
% 1.13/0.67    inference(avatar_contradiction_clause,[],[f275])).
% 1.13/0.67  fof(f275,plain,(
% 1.13/0.67    $false | (~spl7_1 | spl7_2 | ~spl7_5)),
% 1.13/0.67    inference(subsumption_resolution,[],[f274,f48])).
% 1.13/0.67  fof(f48,plain,(
% 1.13/0.67    ~v2_struct_0(sK0)),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f274,plain,(
% 1.13/0.67    v2_struct_0(sK0) | (~spl7_1 | spl7_2 | ~spl7_5)),
% 1.13/0.67    inference(subsumption_resolution,[],[f273,f49])).
% 1.13/0.67  fof(f49,plain,(
% 1.13/0.67    v2_pre_topc(sK0)),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f273,plain,(
% 1.13/0.67    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_1 | spl7_2 | ~spl7_5)),
% 1.13/0.67    inference(subsumption_resolution,[],[f272,f50])).
% 1.13/0.67  fof(f272,plain,(
% 1.13/0.67    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_1 | spl7_2 | ~spl7_5)),
% 1.13/0.67    inference(subsumption_resolution,[],[f271,f240])).
% 1.13/0.67  fof(f240,plain,(
% 1.13/0.67    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | spl7_2),
% 1.13/0.67    inference(forward_demodulation,[],[f99,f65])).
% 1.13/0.67  fof(f65,plain,(
% 1.13/0.67    sK5 = sK6),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f99,plain,(
% 1.13/0.67    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | spl7_2),
% 1.13/0.67    inference(avatar_component_clause,[],[f97])).
% 1.13/0.67  fof(f97,plain,(
% 1.13/0.67    spl7_2 <=> r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 1.13/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.13/0.67  fof(f271,plain,(
% 1.13/0.67    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_1 | ~spl7_5)),
% 1.13/0.67    inference(resolution,[],[f260,f57])).
% 1.13/0.67  fof(f57,plain,(
% 1.13/0.67    m1_pre_topc(sK3,sK0)),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f260,plain,(
% 1.13/0.67    ( ! [X0] : (~m1_pre_topc(sK3,X0) | r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl7_1 | ~spl7_5)),
% 1.13/0.67    inference(subsumption_resolution,[],[f259,f54])).
% 1.13/0.67  fof(f259,plain,(
% 1.13/0.67    ( ! [X0] : (r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl7_1 | ~spl7_5)),
% 1.13/0.67    inference(subsumption_resolution,[],[f258,f62])).
% 1.13/0.67  fof(f62,plain,(
% 1.13/0.67    m1_pre_topc(sK2,sK3)),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f258,plain,(
% 1.13/0.67    ( ! [X0] : (r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl7_1 | ~spl7_5)),
% 1.13/0.67    inference(subsumption_resolution,[],[f257,f102])).
% 1.13/0.67  fof(f102,plain,(
% 1.13/0.67    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.13/0.67    inference(forward_demodulation,[],[f64,f65])).
% 1.13/0.67  fof(f64,plain,(
% 1.13/0.67    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f257,plain,(
% 1.13/0.67    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl7_1 | ~spl7_5)),
% 1.13/0.67    inference(subsumption_resolution,[],[f256,f164])).
% 1.13/0.67  fof(f164,plain,(
% 1.13/0.67    v3_pre_topc(u1_struct_0(sK2),sK3)),
% 1.13/0.67    inference(subsumption_resolution,[],[f163,f149])).
% 1.13/0.67  fof(f149,plain,(
% 1.13/0.67    v2_pre_topc(sK3)),
% 1.13/0.67    inference(subsumption_resolution,[],[f148,f49])).
% 1.13/0.67  fof(f148,plain,(
% 1.13/0.67    v2_pre_topc(sK3) | ~v2_pre_topc(sK0)),
% 1.13/0.67    inference(subsumption_resolution,[],[f144,f50])).
% 1.13/0.67  fof(f144,plain,(
% 1.13/0.67    v2_pre_topc(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.13/0.67    inference(resolution,[],[f74,f57])).
% 1.13/0.67  fof(f74,plain,(
% 1.13/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.13/0.67    inference(cnf_transformation,[],[f24])).
% 1.13/0.67  fof(f24,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.13/0.67    inference(flattening,[],[f23])).
% 1.13/0.67  fof(f23,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.13/0.67    inference(ennf_transformation,[],[f4])).
% 1.13/0.67  fof(f4,axiom,(
% 1.13/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.13/0.67  fof(f163,plain,(
% 1.13/0.67    v3_pre_topc(u1_struct_0(sK2),sK3) | ~v2_pre_topc(sK3)),
% 1.13/0.67    inference(subsumption_resolution,[],[f162,f112])).
% 1.13/0.67  fof(f112,plain,(
% 1.13/0.67    l1_pre_topc(sK3)),
% 1.13/0.67    inference(subsumption_resolution,[],[f109,f50])).
% 1.13/0.67  fof(f109,plain,(
% 1.13/0.67    l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 1.13/0.67    inference(resolution,[],[f69,f57])).
% 1.13/0.67  fof(f162,plain,(
% 1.13/0.67    v3_pre_topc(u1_struct_0(sK2),sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 1.13/0.67    inference(subsumption_resolution,[],[f161,f62])).
% 1.13/0.67  fof(f161,plain,(
% 1.13/0.67    ~m1_pre_topc(sK2,sK3) | v3_pre_topc(u1_struct_0(sK2),sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 1.13/0.67    inference(resolution,[],[f104,f61])).
% 1.13/0.67  fof(f61,plain,(
% 1.13/0.67    v1_tsep_1(sK2,sK3)),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f104,plain,(
% 1.13/0.67    ( ! [X0,X1] : (~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.13/0.67    inference(subsumption_resolution,[],[f91,f70])).
% 1.13/0.67  fof(f70,plain,(
% 1.13/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.13/0.67    inference(cnf_transformation,[],[f18])).
% 1.13/0.67  fof(f18,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.13/0.67    inference(ennf_transformation,[],[f9])).
% 1.13/0.67  fof(f9,axiom,(
% 1.13/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.13/0.67  fof(f91,plain,(
% 1.13/0.67    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.13/0.67    inference(duplicate_literal_removal,[],[f88])).
% 1.13/0.67  fof(f88,plain,(
% 1.13/0.67    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.13/0.67    inference(equality_resolution,[],[f76])).
% 1.13/0.67  fof(f76,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.13/0.67    inference(cnf_transformation,[],[f45])).
% 1.13/0.67  fof(f45,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.13/0.67    inference(flattening,[],[f44])).
% 1.13/0.67  fof(f44,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.13/0.67    inference(nnf_transformation,[],[f28])).
% 1.13/0.67  fof(f28,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.13/0.67    inference(flattening,[],[f27])).
% 1.13/0.67  fof(f27,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.13/0.67    inference(ennf_transformation,[],[f8])).
% 1.13/0.67  fof(f8,axiom,(
% 1.13/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.13/0.67  fof(f256,plain,(
% 1.13/0.67    ( ! [X0] : (~v3_pre_topc(u1_struct_0(sK2),sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl7_1 | ~spl7_5)),
% 1.13/0.67    inference(subsumption_resolution,[],[f255,f128])).
% 1.13/0.67  fof(f128,plain,(
% 1.13/0.67    r2_hidden(sK5,u1_struct_0(sK2)) | ~spl7_5),
% 1.13/0.67    inference(avatar_component_clause,[],[f126])).
% 1.13/0.67  fof(f126,plain,(
% 1.13/0.67    spl7_5 <=> r2_hidden(sK5,u1_struct_0(sK2))),
% 1.13/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.13/0.67  fof(f255,plain,(
% 1.13/0.67    ( ! [X0] : (~r2_hidden(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl7_1),
% 1.13/0.67    inference(resolution,[],[f251,f157])).
% 1.13/0.67  fof(f157,plain,(
% 1.13/0.67    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.13/0.67    inference(subsumption_resolution,[],[f154,f112])).
% 1.13/0.67  fof(f154,plain,(
% 1.13/0.67    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3)),
% 1.13/0.67    inference(resolution,[],[f70,f62])).
% 1.13/0.67  fof(f251,plain,(
% 1.13/0.67    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(sK5,u1_struct_0(X0)) | ~v3_pre_topc(u1_struct_0(X0),sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl7_1),
% 1.13/0.67    inference(resolution,[],[f250,f89])).
% 1.13/0.67  fof(f89,plain,(
% 1.13/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.13/0.67    inference(equality_resolution,[],[f81])).
% 1.13/0.67  fof(f81,plain,(
% 1.13/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.13/0.67    inference(cnf_transformation,[],[f47])).
% 1.13/0.67  fof(f47,plain,(
% 1.13/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.13/0.67    inference(flattening,[],[f46])).
% 1.13/0.67  fof(f46,plain,(
% 1.13/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.13/0.67    inference(nnf_transformation,[],[f1])).
% 1.13/0.67  fof(f1,axiom,(
% 1.13/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.13/0.67  fof(f250,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X2,u1_struct_0(X0)) | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~r2_hidden(sK5,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl7_1),
% 1.13/0.67    inference(subsumption_resolution,[],[f249,f75])).
% 1.13/0.67  fof(f75,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.13/0.67    inference(cnf_transformation,[],[f26])).
% 1.13/0.67  fof(f26,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.13/0.67    inference(flattening,[],[f25])).
% 1.13/0.67  fof(f25,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.13/0.67    inference(ennf_transformation,[],[f10])).
% 1.13/0.67  fof(f10,axiom,(
% 1.13/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.13/0.67  fof(f249,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~r1_tarski(X2,u1_struct_0(X0)) | ~r2_hidden(sK5,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl7_1),
% 1.13/0.67    inference(subsumption_resolution,[],[f248,f51])).
% 1.13/0.67  fof(f51,plain,(
% 1.13/0.67    ~v2_struct_0(sK1)),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f248,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~r1_tarski(X2,u1_struct_0(X0)) | ~r2_hidden(sK5,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl7_1),
% 1.13/0.67    inference(subsumption_resolution,[],[f247,f52])).
% 1.13/0.67  fof(f52,plain,(
% 1.13/0.67    v2_pre_topc(sK1)),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f247,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~r1_tarski(X2,u1_struct_0(X0)) | ~r2_hidden(sK5,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl7_1),
% 1.13/0.67    inference(subsumption_resolution,[],[f246,f53])).
% 1.13/0.67  fof(f53,plain,(
% 1.13/0.67    l1_pre_topc(sK1)),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f246,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~r1_tarski(X2,u1_struct_0(X0)) | ~r2_hidden(sK5,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl7_1),
% 1.13/0.67    inference(subsumption_resolution,[],[f245,f56])).
% 1.13/0.67  fof(f56,plain,(
% 1.13/0.67    ~v2_struct_0(sK3)),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f245,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~r1_tarski(X2,u1_struct_0(X0)) | ~r2_hidden(sK5,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl7_1),
% 1.13/0.67    inference(subsumption_resolution,[],[f244,f58])).
% 1.13/0.67  fof(f58,plain,(
% 1.13/0.67    v1_funct_1(sK4)),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f244,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~r1_tarski(X2,u1_struct_0(X0)) | ~r2_hidden(sK5,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl7_1),
% 1.13/0.67    inference(subsumption_resolution,[],[f243,f59])).
% 1.13/0.67  fof(f59,plain,(
% 1.13/0.67    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f243,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~r1_tarski(X2,u1_struct_0(X0)) | ~r2_hidden(sK5,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl7_1),
% 1.13/0.67    inference(subsumption_resolution,[],[f242,f60])).
% 1.13/0.67  fof(f60,plain,(
% 1.13/0.67    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f242,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~r1_tarski(X2,u1_struct_0(X0)) | ~r2_hidden(sK5,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl7_1),
% 1.13/0.67    inference(subsumption_resolution,[],[f241,f63])).
% 1.13/0.67  fof(f63,plain,(
% 1.13/0.67    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f241,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~r1_tarski(X2,u1_struct_0(X0)) | ~r2_hidden(sK5,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl7_1),
% 1.13/0.67    inference(resolution,[],[f94,f85])).
% 1.13/0.67  fof(f85,plain,(
% 1.13/0.67    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~r1_tmap_1(X3,X1,X4,X7) | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.13/0.67    inference(equality_resolution,[],[f72])).
% 1.13/0.67  fof(f72,plain,(
% 1.13/0.67    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.13/0.67    inference(cnf_transformation,[],[f43])).
% 1.13/0.67  fof(f43,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.13/0.67    inference(nnf_transformation,[],[f22])).
% 1.13/0.67  fof(f22,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.13/0.67    inference(flattening,[],[f21])).
% 1.13/0.67  fof(f21,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.13/0.67    inference(ennf_transformation,[],[f11])).
% 1.13/0.67  fof(f11,axiom,(
% 1.13/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).
% 1.13/0.67  fof(f94,plain,(
% 1.13/0.67    r1_tmap_1(sK3,sK1,sK4,sK5) | ~spl7_1),
% 1.13/0.67    inference(avatar_component_clause,[],[f93])).
% 1.13/0.67  fof(f93,plain,(
% 1.13/0.67    spl7_1 <=> r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.13/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.13/0.67  fof(f239,plain,(
% 1.13/0.67    spl7_1 | ~spl7_2 | ~spl7_5),
% 1.13/0.67    inference(avatar_contradiction_clause,[],[f238])).
% 1.13/0.67  fof(f238,plain,(
% 1.13/0.67    $false | (spl7_1 | ~spl7_2 | ~spl7_5)),
% 1.13/0.67    inference(subsumption_resolution,[],[f237,f89])).
% 1.13/0.67  fof(f237,plain,(
% 1.13/0.67    ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) | (spl7_1 | ~spl7_2 | ~spl7_5)),
% 1.13/0.67    inference(subsumption_resolution,[],[f236,f164])).
% 1.13/0.67  fof(f236,plain,(
% 1.13/0.67    ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) | (spl7_1 | ~spl7_2 | ~spl7_5)),
% 1.13/0.67    inference(subsumption_resolution,[],[f235,f128])).
% 1.13/0.67  fof(f235,plain,(
% 1.13/0.67    ~r2_hidden(sK5,u1_struct_0(sK2)) | ~v3_pre_topc(u1_struct_0(sK2),sK3) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(resolution,[],[f182,f157])).
% 1.13/0.67  fof(f182,plain,(
% 1.13/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~r1_tarski(X0,u1_struct_0(sK2))) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f181,f48])).
% 1.13/0.67  fof(f181,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f180,f49])).
% 1.13/0.67  fof(f180,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f179,f50])).
% 1.13/0.67  fof(f179,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f178,f51])).
% 1.13/0.67  fof(f178,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f177,f52])).
% 1.13/0.67  fof(f177,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f176,f53])).
% 1.13/0.67  fof(f176,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f175,f54])).
% 1.13/0.67  fof(f175,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f174,f55])).
% 1.13/0.67  fof(f174,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f173,f56])).
% 1.13/0.67  fof(f173,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f172,f57])).
% 1.13/0.67  fof(f172,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f171,f58])).
% 1.13/0.67  fof(f171,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f170,f59])).
% 1.13/0.67  fof(f170,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f169,f60])).
% 1.13/0.67  fof(f169,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f168,f62])).
% 1.13/0.67  fof(f168,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f167,f63])).
% 1.13/0.67  fof(f167,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f166,f102])).
% 1.13/0.67  fof(f166,plain,(
% 1.13/0.67    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl7_1 | ~spl7_2)),
% 1.13/0.67    inference(subsumption_resolution,[],[f165,f95])).
% 1.13/0.67  fof(f95,plain,(
% 1.13/0.67    ~r1_tmap_1(sK3,sK1,sK4,sK5) | spl7_1),
% 1.13/0.67    inference(avatar_component_clause,[],[f93])).
% 1.13/0.67  fof(f165,plain,(
% 1.13/0.67    ( ! [X0] : (r1_tmap_1(sK3,sK1,sK4,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK5,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl7_2),
% 1.13/0.67    inference(resolution,[],[f84,f105])).
% 1.13/0.67  fof(f105,plain,(
% 1.13/0.67    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~spl7_2),
% 1.13/0.67    inference(forward_demodulation,[],[f98,f65])).
% 1.13/0.67  fof(f98,plain,(
% 1.13/0.67    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~spl7_2),
% 1.13/0.67    inference(avatar_component_clause,[],[f97])).
% 1.13/0.67  fof(f84,plain,(
% 1.13/0.67    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.13/0.67    inference(equality_resolution,[],[f73])).
% 1.13/0.67  fof(f73,plain,(
% 1.13/0.67    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.13/0.67    inference(cnf_transformation,[],[f43])).
% 1.13/0.67  fof(f133,plain,(
% 1.13/0.67    spl7_5 | spl7_6),
% 1.13/0.67    inference(avatar_split_clause,[],[f114,f130,f126])).
% 1.13/0.67  fof(f114,plain,(
% 1.13/0.67    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(sK5,u1_struct_0(sK2))),
% 1.13/0.67    inference(resolution,[],[f79,f102])).
% 1.13/0.67  fof(f79,plain,(
% 1.13/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.13/0.67    inference(cnf_transformation,[],[f30])).
% 1.13/0.67  fof(f30,plain,(
% 1.13/0.67    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.13/0.67    inference(flattening,[],[f29])).
% 1.13/0.67  fof(f29,plain,(
% 1.13/0.67    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.13/0.67    inference(ennf_transformation,[],[f2])).
% 1.13/0.67  fof(f2,axiom,(
% 1.13/0.67    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.13/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.13/0.67  fof(f101,plain,(
% 1.13/0.67    spl7_1 | spl7_2),
% 1.13/0.67    inference(avatar_split_clause,[],[f66,f97,f93])).
% 1.13/0.67  fof(f66,plain,(
% 1.13/0.67    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  fof(f100,plain,(
% 1.13/0.67    ~spl7_1 | ~spl7_2),
% 1.13/0.67    inference(avatar_split_clause,[],[f67,f97,f93])).
% 1.13/0.67  fof(f67,plain,(
% 1.13/0.67    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.13/0.67    inference(cnf_transformation,[],[f42])).
% 1.13/0.67  % SZS output end Proof for theBenchmark
% 1.13/0.67  % (4870)------------------------------
% 1.13/0.67  % (4870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.67  % (4870)Termination reason: Refutation
% 1.13/0.67  
% 1.13/0.67  % (4870)Memory used [KB]: 10874
% 1.13/0.67  % (4870)Time elapsed: 0.087 s
% 1.13/0.67  % (4870)------------------------------
% 1.13/0.67  % (4870)------------------------------
% 1.13/0.68  % (4662)Success in time 0.309 s
%------------------------------------------------------------------------------
