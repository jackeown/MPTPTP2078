%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 (1015 expanded)
%              Number of leaves         :   13 ( 494 expanded)
%              Depth                    :   35
%              Number of atoms          : 1143 (22385 expanded)
%              Number of equality atoms :   28 (1274 expanded)
%              Maximal formula depth    :   28 (  10 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f64,f125,f146])).

fof(f146,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f144,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f15,f22,f21,f20,f19,f18,f17,f16])).

fof(f16,plain,
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

fof(f17,plain,
    ( ? [X1] :
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
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,sK0,X4,X5) )
                          & ( r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6)
                            | r1_tmap_1(X3,sK0,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X2,sK1)
                  & v1_tsep_1(X2,sK1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6)
                          | ~ r1_tmap_1(X3,sK0,X4,X5) )
                        & ( r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6)
                          | r1_tmap_1(X3,sK0,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(X2,sK1)
                & v1_tsep_1(X2,sK1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6)
                        | ~ r1_tmap_1(X3,sK0,X4,X5) )
                      & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6)
                        | r1_tmap_1(X3,sK0,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK2,X3)
              & m1_pre_topc(sK2,sK1)
              & v1_tsep_1(sK2,sK1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6)
                      | ~ r1_tmap_1(X3,sK0,X4,X5) )
                    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6)
                      | r1_tmap_1(X3,sK0,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK2)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK2,X3)
            & m1_pre_topc(sK2,sK1)
            & v1_tsep_1(sK2,sK1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6)
                    | ~ r1_tmap_1(sK3,sK0,X4,X5) )
                  & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6)
                    | r1_tmap_1(sK3,sK0,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK2)) )
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & m1_pre_topc(sK2,sK3)
          & m1_pre_topc(sK2,sK1)
          & v1_tsep_1(sK2,sK1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6)
                  | ~ r1_tmap_1(sK3,sK0,X4,X5) )
                & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6)
                  | r1_tmap_1(sK3,sK0,X4,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK2)) )
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & m1_pre_topc(sK2,sK3)
        & m1_pre_topc(sK2,sK1)
        & v1_tsep_1(sK2,sK1)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
                | ~ r1_tmap_1(sK3,sK0,sK4,X5) )
              & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
                | r1_tmap_1(sK3,sK0,sK4,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK2)) )
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & m1_pre_topc(sK2,sK3)
      & m1_pre_topc(sK2,sK1)
      & v1_tsep_1(sK2,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
              | ~ r1_tmap_1(sK3,sK0,sK4,X5) )
            & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
              | r1_tmap_1(sK3,sK0,sK4,X5) )
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK2)) )
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ? [X6] :
          ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
            | ~ r1_tmap_1(sK3,sK0,sK4,sK5) )
          & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
            | r1_tmap_1(sK3,sK0,sK4,sK5) )
          & sK5 = X6
          & m1_subset_1(X6,u1_struct_0(sK2)) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X6] :
        ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
          | ~ r1_tmap_1(sK3,sK0,sK4,sK5) )
        & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
          | r1_tmap_1(sK3,sK0,sK4,sK5) )
        & sK5 = X6
        & m1_subset_1(X6,u1_struct_0(sK2)) )
   => ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
        | ~ r1_tmap_1(sK3,sK0,sK4,sK5) )
      & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
        | r1_tmap_1(sK3,sK0,sK4,sK5) )
      & sK5 = sK6
      & m1_subset_1(sK6,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tmap_1)).

fof(f144,plain,
    ( v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f143,f30])).

fof(f30,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f143,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f142,f31])).

fof(f31,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f142,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f141,f26])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f141,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f140,f27])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f140,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f139,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f139,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f138,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f138,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f137,f40])).

fof(f40,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f137,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f136,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f136,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f135,f35])).

fof(f35,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f135,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f134,f36])).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f134,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f133,f37])).

fof(f37,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f133,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f132,f38])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f23])).

fof(f132,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f131,f123])).

fof(f123,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f122,f40])).

fof(f122,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f121,f39])).

fof(f39,plain,(
    v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f121,plain,
    ( ~ v1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | v1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f114,f41])).

fof(f41,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ v1_tsep_1(X0,sK1)
      | ~ m1_pre_topc(X0,sK1)
      | v1_tsep_1(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f113,f29])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ v1_tsep_1(X0,sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X0,sK3)
      | v1_tsep_1(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f112,f30])).

fof(f112,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ v1_tsep_1(X0,sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X0,sK3)
      | v1_tsep_1(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f111,f31])).

fof(f111,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ v1_tsep_1(X0,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X0,sK3)
      | v1_tsep_1(X0,sK3) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ v1_tsep_1(X0,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X0,sK3)
      | v1_tsep_1(X0,sK3)
      | ~ m1_pre_topc(X0,sK1) ) ),
    inference(resolution,[],[f95,f35])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | v1_tsep_1(X1,sK3)
      | ~ m1_pre_topc(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f94,f30])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | v1_tsep_1(X1,sK3)
      | ~ m1_pre_topc(X1,sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f93,f31])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | v1_tsep_1(X1,sK3)
      | ~ m1_pre_topc(X1,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f90,f34])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | v1_tsep_1(X1,sK3)
      | ~ m1_pre_topc(X1,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(resolution,[],[f68,f35])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X2)
      | ~ v1_tsep_1(X0,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,X1)
      | v1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X0,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3) ) ),
    inference(resolution,[],[f49,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | v1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).

fof(f131,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f130,f41])).

fof(f130,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f129,f42])).

fof(f42,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f129,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f128,f65])).

fof(f65,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f43,f44])).

fof(f44,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f128,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f127,f62])).

fof(f62,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl7_1
  <=> r1_tmap_1(sK3,sK0,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f127,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_2 ),
    inference(resolution,[],[f126,f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ r1_tmap_1(X3,X1,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ r1_tmap_1(X3,X1,X4,X5)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X1,X4,X5)
                                  | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(ennf_transformation,[],[f3])).

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

fof(f126,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | spl7_2 ),
    inference(forward_demodulation,[],[f60,f44])).

fof(f60,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl7_2
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f125,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f123,f87])).

fof(f87,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f86,f29])).

fof(f86,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f85,f30])).

fof(f85,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f84,f31])).

fof(f84,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f83,f26])).

fof(f83,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f82,f27])).

fof(f82,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f81,f28])).

fof(f81,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f80,f32])).

fof(f80,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f79,f40])).

fof(f79,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f78,f34])).

fof(f78,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f77,f35])).

fof(f77,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f76,f36])).

fof(f76,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f75,f37])).

fof(f75,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f74,f38])).

fof(f74,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f73,f41])).

fof(f73,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f72,f42])).

fof(f72,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f71,f65])).

fof(f71,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f70,f57])).

fof(f57,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f70,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_2 ),
    inference(resolution,[],[f53,f66])).

fof(f66,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f63,f44])).

fof(f63,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f59])).

% (14833)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f53,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X5)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f45,f59,f56])).

fof(f45,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f46,f59,f56])).

fof(f46,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:12:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (14828)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.43  % (14828)Refutation not found, incomplete strategy% (14828)------------------------------
% 0.21/0.43  % (14828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (14828)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.43  
% 0.21/0.43  % (14828)Memory used [KB]: 1663
% 0.21/0.43  % (14828)Time elapsed: 0.005 s
% 0.21/0.43  % (14828)------------------------------
% 0.21/0.43  % (14828)------------------------------
% 0.21/0.44  % (14817)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.44  % (14825)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.45  % (14817)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f147,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f61,f64,f125,f146])).
% 0.21/0.45  fof(f146,plain,(
% 0.21/0.45    ~spl7_1 | spl7_2),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f145])).
% 0.21/0.45  fof(f145,plain,(
% 0.21/0.45    $false | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f144,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ~v2_struct_0(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    (((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f15,f22,f21,f20,f19,f18,f17,f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK1) & v1_tsep_1(X2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK1) & v1_tsep_1(X2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6) | ~r1_tmap_1(sK3,sK0,X4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6) | r1_tmap_1(sK3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6) | ~r1_tmap_1(sK3,sK0,X4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6) | r1_tmap_1(sK3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK0,sK4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK0,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK0,sK4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK0,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f6])).
% 0.21/0.45  fof(f6,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,negated_conjecture,(
% 0.21/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.21/0.45    inference(negated_conjecture,[],[f4])).
% 0.21/0.45  fof(f4,conjecture,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tmap_1)).
% 0.21/0.45  fof(f144,plain,(
% 0.21/0.45    v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f143,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    v2_pre_topc(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f143,plain,(
% 0.21/0.45    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f142,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    l1_pre_topc(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f142,plain,(
% 0.21/0.45    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f141,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ~v2_struct_0(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f141,plain,(
% 0.21/0.45    v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f140,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    v2_pre_topc(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f140,plain,(
% 0.21/0.45    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f139,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    l1_pre_topc(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f139,plain,(
% 0.21/0.45    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f138,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ~v2_struct_0(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f138,plain,(
% 0.21/0.45    v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f137,f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    m1_pre_topc(sK2,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f137,plain,(
% 0.21/0.45    ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f136,f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ~v2_struct_0(sK3)),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f136,plain,(
% 0.21/0.45    v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f135,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    m1_pre_topc(sK3,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f135,plain,(
% 0.21/0.45    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f134,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    v1_funct_1(sK4)),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f134,plain,(
% 0.21/0.45    ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f133,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f133,plain,(
% 0.21/0.45    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f132,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f132,plain,(
% 0.21/0.45    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f131,f123])).
% 0.21/0.45  fof(f123,plain,(
% 0.21/0.45    v1_tsep_1(sK2,sK3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f122,f40])).
% 0.21/0.45  fof(f122,plain,(
% 0.21/0.45    ~m1_pre_topc(sK2,sK1) | v1_tsep_1(sK2,sK3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f121,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    v1_tsep_1(sK2,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f121,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK1) | ~m1_pre_topc(sK2,sK1) | v1_tsep_1(sK2,sK3)),
% 0.21/0.45    inference(resolution,[],[f114,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    m1_pre_topc(sK2,sK3)),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~v1_tsep_1(X0,sK1) | ~m1_pre_topc(X0,sK1) | v1_tsep_1(X0,sK3)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f113,f29])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_pre_topc(X0,sK1) | ~v1_tsep_1(X0,sK1) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK3) | v1_tsep_1(X0,sK3)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f112,f30])).
% 0.21/0.45  fof(f112,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_pre_topc(X0,sK1) | ~v1_tsep_1(X0,sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK3) | v1_tsep_1(X0,sK3)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f111,f31])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_pre_topc(X0,sK1) | ~v1_tsep_1(X0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK3) | v1_tsep_1(X0,sK3)) )),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f110])).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_pre_topc(X0,sK1) | ~v1_tsep_1(X0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK3) | v1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK1)) )),
% 0.21/0.45    inference(resolution,[],[f95,f35])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f94,f30])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK1) | ~v2_pre_topc(sK1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f93,f31])).
% 0.21/0.45  fof(f93,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f90,f34])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_pre_topc(sK3,X0) | v2_struct_0(sK3) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)) )),
% 0.21/0.45    inference(resolution,[],[f68,f35])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X1,X3) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | ~v1_tsep_1(X0,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~m1_pre_topc(X0,X1) | v1_tsep_1(X0,X1) | ~m1_pre_topc(X0,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) )),
% 0.21/0.45    inference(resolution,[],[f49,f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.45    inference(flattening,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).
% 0.21/0.45  fof(f131,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f130,f41])).
% 0.21/0.45  fof(f130,plain,(
% 0.21/0.45    ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f129,f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f129,plain,(
% 0.21/0.45    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f128,f65])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.45    inference(forward_demodulation,[],[f43,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    sK5 = sK6),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f128,plain,(
% 0.21/0.45    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl7_1 | spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f127,f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    r1_tmap_1(sK3,sK0,sK4,sK5) | ~spl7_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    spl7_1 <=> r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.45  fof(f127,plain,(
% 0.21/0.45    ~r1_tmap_1(sK3,sK0,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl7_2),
% 0.21/0.45    inference(resolution,[],[f126,f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(equality_resolution,[],[f47])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.21/0.45  fof(f126,plain,(
% 0.21/0.45    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | spl7_2),
% 0.21/0.45    inference(forward_demodulation,[],[f60,f44])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | spl7_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    spl7_2 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.45  fof(f125,plain,(
% 0.21/0.45    spl7_1 | ~spl7_2),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f124])).
% 0.21/0.45  fof(f124,plain,(
% 0.21/0.45    $false | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f123,f87])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK3) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f86,f29])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f85,f30])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK3) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f84,f31])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f83,f26])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f82,f27])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f81,f28])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f80,f32])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f79,f40])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f78,f34])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f77,f35])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f76,f36])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK3) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f75,f37])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f74,f38])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f73,f41])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f72,f42])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f71,f65])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl7_1 | ~spl7_2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f70,f57])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    ~r1_tmap_1(sK3,sK0,sK4,sK5) | spl7_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f56])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    r1_tmap_1(sK3,sK0,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl7_2),
% 0.21/0.45    inference(resolution,[],[f53,f66])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | ~spl7_2),
% 0.21/0.45    inference(forward_demodulation,[],[f63,f44])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~spl7_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f59])).
% 0.21/0.45  % (14833)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(equality_resolution,[],[f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f24])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    spl7_1 | spl7_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f45,f59,f56])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ~spl7_1 | ~spl7_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f46,f59,f56])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (14817)------------------------------
% 0.21/0.45  % (14817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (14817)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (14817)Memory used [KB]: 10746
% 0.21/0.45  % (14817)Time elapsed: 0.066 s
% 0.21/0.45  % (14817)------------------------------
% 0.21/0.45  % (14817)------------------------------
% 0.21/0.45  % (14814)Success in time 0.1 s
%------------------------------------------------------------------------------
