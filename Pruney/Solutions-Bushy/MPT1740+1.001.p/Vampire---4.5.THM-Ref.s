%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1740+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:28 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 588 expanded)
%              Number of leaves         :   17 ( 212 expanded)
%              Depth                    :   25
%              Number of atoms          : 1048 (7712 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   30 (  10 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f68,f121,f130,f150])).

fof(f150,plain,
    ( ~ spl9_1
    | spl9_2
    | ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f147,f63])).

fof(f63,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl9_3
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f147,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl9_1
    | spl9_2 ),
    inference(resolution,[],[f146,f58])).

fof(f58,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK3)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl9_2
  <=> r1_tmap_1(sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f146,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f145,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ( ~ r1_tmap_1(sK1,sK0,sK2,sK3)
        & m1_subset_1(sK3,u1_struct_0(sK1)) )
      | ~ v5_pre_topc(sK2,sK1,sK0) )
    & ( ! [X4] :
          ( r1_tmap_1(sK1,sK0,sK2,X4)
          | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
      | v5_pre_topc(sK2,sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f17,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | v5_pre_topc(X2,X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
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
                    ( ~ r1_tmap_1(X1,sK0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,sK0) )
              & ( ! [X4] :
                    ( r1_tmap_1(X1,sK0,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r1_tmap_1(X1,sK0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ v5_pre_topc(X2,X1,sK0) )
            & ( ! [X4] :
                  ( r1_tmap_1(X1,sK0,X2,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | v5_pre_topc(X2,X1,sK0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r1_tmap_1(sK1,sK0,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK1)) )
            | ~ v5_pre_topc(X2,sK1,sK0) )
          & ( ! [X4] :
                ( r1_tmap_1(sK1,sK0,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
            | v5_pre_topc(X2,sK1,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ~ r1_tmap_1(sK1,sK0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(sK1)) )
          | ~ v5_pre_topc(X2,sK1,sK0) )
        & ( ! [X4] :
              ( r1_tmap_1(sK1,sK0,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
          | v5_pre_topc(X2,sK1,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X2) )
   => ( ( ? [X3] :
            ( ~ r1_tmap_1(sK1,sK0,sK2,X3)
            & m1_subset_1(X3,u1_struct_0(sK1)) )
        | ~ v5_pre_topc(sK2,sK1,sK0) )
      & ( ! [X4] :
            ( r1_tmap_1(sK1,sK0,sK2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
        | v5_pre_topc(sK2,sK1,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X3] :
        ( ~ r1_tmap_1(sK1,sK0,sK2,X3)
        & m1_subset_1(X3,u1_struct_0(sK1)) )
   => ( ~ r1_tmap_1(sK1,sK0,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,X0) )
              & ( ! [X4] :
                    ( r1_tmap_1(X1,X0,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,X0) )
              & ( ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,X0) )
              & ( ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <~> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <~> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
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

fof(f145,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f144,f34])).

fof(f34,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f143,f35])).

fof(f35,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f142,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f141,f31])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f140,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f139,f36])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f138,f37])).

fof(f37,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | r1_tmap_1(sK1,sK0,sK2,X0) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f137,f53])).

fof(f53,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl9_1
  <=> v5_pre_topc(sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f137,plain,(
    ! [X0] :
      ( ~ v5_pre_topc(sK2,sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | r1_tmap_1(sK1,sK0,sK2,X0) ) ),
    inference(resolution,[],[f136,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
      | ~ v5_pre_topc(X2,X1,X3)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,X3,X2,X0) ) ),
    inference(subsumption_resolution,[],[f135,f81])).

fof(f81,plain,(
    ! [X6,X4,X5,X3] :
      ( m1_connsp_2(sK6(X3,X4,X5,X6,sK7(X3,X4,X5,X6)),X3,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_pre_topc(X5,X3,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tmap_1(X3,X4,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X6,X4,X5,X3] :
      ( m1_connsp_2(sK6(X3,X4,X5,X6,sK7(X3,X4,X5,X6)),X3,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_pre_topc(X5,X3,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tmap_1(X3,X4,X5,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f42,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_connsp_2(sK7(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ( ! [X5] :
                            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK7(X0,X1,X2,X3))
                            | ~ m1_connsp_2(X5,X0,X3) )
                        & m1_connsp_2(sK7(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                    & ( ! [X6] :
                          ( ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK8(X0,X1,X2,X3,X6)),X6)
                            & m1_connsp_2(sK8(X0,X1,X2,X3,X6),X0,X3) )
                          | ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f26,f28,f27])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
              | ~ m1_connsp_2(X5,X0,X3) )
          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
     => ( ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK7(X0,X1,X2,X3))
            | ~ m1_connsp_2(X5,X0,X3) )
        & m1_connsp_2(sK7(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X6,X3,X2,X1,X0] :
      ( ? [X7] :
          ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6)
          & m1_connsp_2(X7,X0,X3) )
     => ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK8(X0,X1,X2,X3,X6)),X6)
        & m1_connsp_2(sK8(X0,X1,X2,X3,X6),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                    & ( ! [X6] :
                          ( ? [X7] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6)
                              & m1_connsp_2(X7,X0,X3) )
                          | ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                    & ( ! [X4] :
                          ( ? [X5] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              & m1_connsp_2(X5,X0,X3) )
                          | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                       => ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tmap_1)).

fof(f42,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6))
      | m1_connsp_2(sK6(X0,X1,X2,X6,X7),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v5_pre_topc(X2,X0,X1)
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

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ! [X5] :
                        ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK5(X0,X1,X2))
                        | ~ m1_connsp_2(X5,X0,sK4(X0,X1,X2)) )
                    & m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))
                    & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ! [X7] :
                          ( ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2,X6,X7)),X7)
                            & m1_connsp_2(sK6(X0,X1,X2,X6,X7),X0,X6) )
                          | ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                  | ~ m1_connsp_2(X5,X0,X3) )
              & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ! [X5] :
                ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                | ~ m1_connsp_2(X5,X0,sK4(X0,X1,X2)) )
            & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
              | ~ m1_connsp_2(X5,X0,sK4(X0,X1,X2)) )
          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))) )
     => ( ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK5(X0,X1,X2))
            | ~ m1_connsp_2(X5,X0,sK4(X0,X1,X2)) )
        & m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X7,X6,X2,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X8),X7)
          & m1_connsp_2(X8,X0,X6) )
     => ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2,X6,X7)),X7)
        & m1_connsp_2(sK6(X0,X1,X2,X6,X7),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ! [X7] :
                          ( ? [X8] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X8),X7)
                              & m1_connsp_2(X8,X0,X6) )
                          | ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ! [X4] :
                          ( ? [X5] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              & m1_connsp_2(X5,X0,X3) )
                          | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                       => ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_borsuk_1)).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X1,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,X3,X2,X0)
      | ~ m1_connsp_2(sK6(X1,X3,X2,X0,sK7(X1,X3,X2,X0)),X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X1,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,X3,X2,X0)
      | ~ m1_connsp_2(sK6(X1,X3,X2,X0,sK7(X1,X3,X2,X0)),X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r1_tmap_1(X1,X3,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f94,f49])).

fof(f94,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( ~ m1_connsp_2(sK7(X4,X5,X6,X7),X5,k3_funct_2(u1_struct_0(X4),u1_struct_0(X5),X6,X8))
      | ~ m1_subset_1(X8,u1_struct_0(X4))
      | ~ v5_pre_topc(X6,X4,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | r1_tmap_1(X4,X5,X6,X7)
      | ~ m1_connsp_2(sK6(X4,X5,X6,X8,sK7(X4,X5,X6,X7)),X4,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( ~ m1_connsp_2(sK7(X4,X5,X6,X7),X5,k3_funct_2(u1_struct_0(X4),u1_struct_0(X5),X6,X8))
      | ~ m1_subset_1(X8,u1_struct_0(X4))
      | ~ v5_pre_topc(X6,X4,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | r1_tmap_1(X4,X5,X6,X7)
      | ~ m1_connsp_2(sK6(X4,X5,X6,X8,sK7(X4,X5,X6,X7)),X4,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f43,f50])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK7(X0,X1,X2,X3))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_connsp_2(X5,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2,X6,X7)),X7)
      | ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v5_pre_topc(X2,X0,X1)
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

fof(f130,plain,
    ( spl9_1
    | spl9_5 ),
    inference(avatar_split_clause,[],[f129,f118,f52])).

fof(f118,plain,
    ( spl9_5
  <=> m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f129,plain,
    ( m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f128,f33])).

fof(f128,plain,
    ( m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f127,f34])).

fof(f127,plain,
    ( m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f126,f35])).

fof(f126,plain,
    ( m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f125,f30])).

fof(f125,plain,
    ( m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f124,f31])).

fof(f124,plain,
    ( m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f123,f32])).

fof(f123,plain,
    ( m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f122,f36])).

fof(f122,plain,
    ( m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f69,f37])).

fof(f69,plain,
    ( m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f44,f38])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f121,plain,
    ( ~ spl9_5
    | spl9_1
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f113,f66,f52,f118])).

fof(f66,plain,
    ( spl9_4
  <=> ! [X4] :
        ( r1_tmap_1(sK1,sK0,sK2,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f113,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f112,f33])).

fof(f112,plain,
    ( v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f111,f34])).

fof(f111,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f110,f35])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f109,f30])).

fof(f109,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f108,f31])).

fof(f108,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f107,f32])).

fof(f107,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f106,f36])).

fof(f106,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f105,f37])).

fof(f105,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f104,f38])).

fof(f104,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | ~ spl9_4 ),
    inference(resolution,[],[f103,f67])).

fof(f67,plain,
    ( ! [X4] :
        ( r1_tmap_1(sK1,sK0,sK2,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X0,X1,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f102,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))
      | v5_pre_topc(X2,X0,X1)
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

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X0,X1,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))) ) ),
    inference(subsumption_resolution,[],[f101,f44])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X0,X1,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X0,X1,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))
      | ~ r1_tmap_1(X0,X1,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(resolution,[],[f99,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK8(X0,X1,X2,sK4(X0,X1,X2),sK5(X0,X1,X2)),X0,sK4(X0,X1,X2))
      | ~ r1_tmap_1(X0,X1,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f90,f44])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK8(X0,X1,X2,sK4(X0,X1,X2),sK5(X0,X1,X2)),X0,sK4(X0,X1,X2))
      | ~ r1_tmap_1(X0,X1,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK8(X0,X1,X2,sK4(X0,X1,X2),sK5(X0,X1,X2)),X0,sK4(X0,X1,X2))
      | ~ r1_tmap_1(X0,X1,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f47,f45])).

fof(f47,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | m1_connsp_2(sK8(X0,X1,X2,X3,X6),X0,X3)
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(sK8(X0,X1,X2,X3,sK5(X0,X1,X2)),X0,sK4(X0,X1,X2))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_connsp_2(sK8(X0,X1,X2,X3,sK5(X0,X1,X2)),X0,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f48,f46])).

fof(f46,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK5(X0,X1,X2))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_connsp_2(X5,X0,sK4(X0,X1,X2))
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

fof(f48,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK8(X0,X1,X2,X3,X6)),X6)
      | ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,
    ( spl9_1
    | spl9_4 ),
    inference(avatar_split_clause,[],[f39,f66,f52])).

fof(f39,plain,(
    ! [X4] :
      ( r1_tmap_1(sK1,sK0,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v5_pre_topc(sK2,sK1,sK0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,
    ( ~ spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f40,f61,f52])).

fof(f40,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f41,f56,f52])).

fof(f41,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ v5_pre_topc(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------
