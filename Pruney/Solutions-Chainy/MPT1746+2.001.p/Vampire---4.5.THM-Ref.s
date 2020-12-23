%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 552 expanded)
%              Number of leaves         :    9 ( 194 expanded)
%              Depth                    :   32
%              Number of atoms          :  657 (9830 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f68,f98])).

fof(f98,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f96,f81])).

fof(f81,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f80,f41])).

fof(f41,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl5_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f80,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f79,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
        & m1_subset_1(sK3,u1_struct_0(sK0)) )
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2) )
    & ( ! [X4] :
          ( r1_tmap_1(sK0,sK1,sK2,X4)
          | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
      | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v5_pre_topc(sK2,sK0,sK1)
        & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(sK2) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f14,f13,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r1_tmap_1(X0,X1,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(X2) )
                & ( ! [X4] :
                      ( r1_tmap_1(X0,X1,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v5_pre_topc(X2,X0,X1)
                    & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X2) ) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(sK0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                | ~ v5_pre_topc(X2,sK0,X1)
                | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
              & ( ! [X4] :
                    ( r1_tmap_1(sK0,X1,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
                | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,sK0,X1)
                  & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                  & v1_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r1_tmap_1(sK0,X1,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,sK0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
            & ( ! [X4] :
                  ( r1_tmap_1(sK0,X1,X2,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
              | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                & v5_pre_topc(X2,sK0,X1)
                & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                & v1_funct_1(X2) ) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r1_tmap_1(sK0,sK1,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            | ~ v5_pre_topc(X2,sK0,sK1)
            | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
            | ~ v1_funct_1(X2) )
          & ( ! [X4] :
                ( r1_tmap_1(sK0,sK1,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
            | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v5_pre_topc(X2,sK0,sK1)
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X2) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ~ r1_tmap_1(sK0,sK1,X2,X3)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          | ~ v5_pre_topc(X2,sK0,sK1)
          | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          | ~ v1_funct_1(X2) )
        & ( ! [X4] :
              ( r1_tmap_1(sK0,sK1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
          | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v5_pre_topc(X2,sK0,sK1)
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X2) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( ? [X3] :
            ( ~ r1_tmap_1(sK0,sK1,sK2,X3)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2) )
      & ( ! [X4] :
            ( r1_tmap_1(sK0,sK1,sK2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
        | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v5_pre_topc(sK2,sK0,sK1)
          & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(sK2) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X3] :
        ( ~ r1_tmap_1(sK0,sK1,sK2,X3)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(X2,X0,X1)
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
              & ( ! [X4] :
                    ( r1_tmap_1(X0,X1,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(X2,X0,X1)
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
              & ( ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(X2,X0,X1)
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
              & ( ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              <~> ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              <~> ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
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
               => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v5_pre_topc(X2,X0,X1)
                    & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X2) )
                <=> ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => r1_tmap_1(X0,X1,X2,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
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
             => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => r1_tmap_1(X0,X1,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tmap_1)).

fof(f79,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f78,f27])).

fof(f27,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f33,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f96,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f95,f82])).

fof(f82,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f77,f41])).

fof(f77,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f76,f26])).

fof(f76,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f75,f27])).

fof(f75,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f34,f28])).

fof(f34,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f95,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK0,sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f94,f23])).

fof(f23,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK2,X0)
        | v2_struct_0(sK1) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f93,f24])).

fof(f24,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK2,X0)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f92,f25])).

fof(f25,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK2,X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f91,f20])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK2,X0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f90,f21])).

fof(f21,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK2,X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f89,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_tmap_1(sK0,sK1,sK2,X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f88,f27])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | r1_tmap_1(sK0,sK1,sK2,X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f87,f41])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f86,f28])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v5_pre_topc(sK2,X1,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X2))
      | r1_tmap_1(X1,X2,sK2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f35,f26])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | r1_tmap_1(X1,X0,X2,X4)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2))
                    & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

fof(f68,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f66,f23])).

fof(f66,plain,
    ( v2_struct_0(sK1)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f65,f24])).

fof(f65,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f64,f25])).

fof(f64,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f63,f20])).

fof(f63,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f62,f21])).

fof(f62,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f61,f22])).

fof(f61,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f60,f26])).

fof(f60,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f59,f27])).

fof(f59,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f58,f28])).

fof(f58,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f57,f40])).

fof(f40,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f57,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f56,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
      | v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f55,f44])).

fof(f44,plain,
    ( ! [X4] :
        ( r1_tmap_1(sK0,sK1,sK2,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl5_2
  <=> ! [X4] :
        ( r1_tmap_1(sK0,sK1,sK2,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f55,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f54,f23])).

fof(f54,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2))
    | v2_struct_0(sK1)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f53,f24])).

fof(f53,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f52,f25])).

fof(f52,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f51,f20])).

fof(f51,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f50,f21])).

fof(f50,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f49,f22])).

fof(f49,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f48,f40])).

fof(f48,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f47,f27])).

fof(f47,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f46,f28])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ r1_tmap_1(X0,X1,sK2,sK4(X1,X0,sK2))
      | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(sK2,X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f37,f26])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | v5_pre_topc(X2,X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f31,f43,f39])).

fof(f31,plain,(
    ! [X4] :
      ( r1_tmap_1(sK0,sK1,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (3751)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (3750)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (3745)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.47  % (3745)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f45,f68,f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ~spl5_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f97])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    $false | ~spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f96,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f80,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    v5_pre_topc(sK2,sK0,sK1) | ~spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    spl5_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    m1_subset_1(sK3,u1_struct_0(sK0)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f79,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ((((~r1_tmap_1(sK0,sK1,sK2,sK3) & m1_subset_1(sK3,u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)) & (! [X4] : (r1_tmap_1(sK0,sK1,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0))) | (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f14,f13,f12,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X0,X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & (! [X4] : (r1_tmap_1(X0,X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(sK0,X1,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK0,X1) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & (! [X4] : (r1_tmap_1(sK0,X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X2,sK0,X1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(sK0,X1,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK0,X1) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & (! [X4] : (r1_tmap_1(sK0,X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X2,sK0,X1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : ((? [X3] : (~r1_tmap_1(sK0,sK1,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X2,sK0,sK1) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X2)) & (! [X4] : (r1_tmap_1(sK0,sK1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X2,sK0,sK1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X2] : ((? [X3] : (~r1_tmap_1(sK0,sK1,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X2,sK0,sK1) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X2)) & (! [X4] : (r1_tmap_1(sK0,sK1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X2,sK0,sK1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((? [X3] : (~r1_tmap_1(sK0,sK1,sK2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)) & (! [X4] : (r1_tmap_1(sK0,sK1,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0))) | (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X3] : (~r1_tmap_1(sK0,sK1,sK2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) => (~r1_tmap_1(sK0,sK1,sK2,sK3) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X0,X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & (! [X4] : (r1_tmap_1(X0,X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(rectify,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X0,X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & (! [X3] : (r1_tmap_1(X0,X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (((? [X3] : (~r1_tmap_1(X0,X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & (! [X3] : (r1_tmap_1(X0,X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> ! [X3] : (r1_tmap_1(X0,X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f4])).
% 0.21/0.47  fof(f4,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> ! [X3] : (r1_tmap_1(X0,X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => r1_tmap_1(X0,X1,X2,X3))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f2])).
% 0.21/0.47  fof(f2,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => r1_tmap_1(X0,X1,X2,X3))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tmap_1)).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    m1_subset_1(sK3,u1_struct_0(sK0)) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f78,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    m1_subset_1(sK3,u1_struct_0(sK0)) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f33,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl5_1),
% 0.21/0.47    inference(resolution,[],[f95,f82])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ~r1_tmap_1(sK0,sK1,sK2,sK3) | ~spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f77,f41])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ~r1_tmap_1(sK0,sK1,sK2,sK3) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f76,f26])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ~r1_tmap_1(sK0,sK1,sK2,sK3) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f75,f27])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ~r1_tmap_1(sK0,sK1,sK2,sK3) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f34,f28])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ~r1_tmap_1(sK0,sK1,sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tmap_1(sK0,sK1,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f94,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ~v2_struct_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK2,X0) | v2_struct_0(sK1)) ) | ~spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f93,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    v2_pre_topc(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK2,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f92,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    l1_pre_topc(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK2,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f91,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK2,X0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f90,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK2,X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f89,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK2,X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f88,f27])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | r1_tmap_1(sK0,sK1,sK2,X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f87,f41])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ( ! [X0] : (~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | r1_tmap_1(sK0,sK1,sK2,X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.21/0.47    inference(resolution,[],[f86,f28])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v5_pre_topc(sK2,X1,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X2)) | r1_tmap_1(X1,X2,sK2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 0.21/0.47    inference(resolution,[],[f35,f26])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~v5_pre_topc(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | r1_tmap_1(X1,X0,X2,X4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | (~r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(rectify,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl5_1 | ~spl5_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f67])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    $false | (spl5_1 | ~spl5_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f66,f23])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    v2_struct_0(sK1) | (spl5_1 | ~spl5_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f65,f24])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl5_1 | ~spl5_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f64,f25])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl5_1 | ~spl5_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f63,f20])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl5_1 | ~spl5_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f62,f21])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl5_1 | ~spl5_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f61,f22])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl5_1 | ~spl5_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f60,f26])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl5_1 | ~spl5_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f59,f27])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl5_1 | ~spl5_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f58,f28])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl5_1 | ~spl5_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f57,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ~v5_pre_topc(sK2,sK0,sK1) | spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f39])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl5_1 | ~spl5_2)),
% 0.21/0.47    inference(resolution,[],[f56,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) | v5_pre_topc(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0)) | (spl5_1 | ~spl5_2)),
% 0.21/0.47    inference(resolution,[],[f55,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X4] : (r1_tmap_1(sK0,sK1,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | ~spl5_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl5_2 <=> ! [X4] : (r1_tmap_1(sK0,sK1,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ~r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2)) | spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f54,f23])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2)) | v2_struct_0(sK1) | spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f53,f24])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ~r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f52,f25])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ~r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f51,f20])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ~r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2)) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f50,f21])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ~r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f49,f22])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ~r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl5_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f48,f40])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ~r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2)) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f47,f27])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ~r1_tmap_1(sK0,sK1,sK2,sK4(sK1,sK0,sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.21/0.47    inference(resolution,[],[f46,f28])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~r1_tmap_1(X0,X1,sK2,sK4(X1,X0,sK2)) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.47    inference(resolution,[],[f37,f26])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | v5_pre_topc(X2,X1,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    spl5_1 | spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f43,f39])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X4] : (r1_tmap_1(sK0,sK1,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v5_pre_topc(sK2,sK0,sK1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (3745)------------------------------
% 0.21/0.47  % (3745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (3745)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (3745)Memory used [KB]: 5373
% 0.21/0.47  % (3745)Time elapsed: 0.061 s
% 0.21/0.47  % (3745)------------------------------
% 0.21/0.47  % (3745)------------------------------
% 0.21/0.47  % (3744)Success in time 0.11 s
%------------------------------------------------------------------------------
