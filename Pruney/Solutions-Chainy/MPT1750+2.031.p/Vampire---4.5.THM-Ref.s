%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 336 expanded)
%              Number of leaves         :   24 ( 148 expanded)
%              Depth                    :   16
%              Number of atoms          :  434 (3447 expanded)
%              Number of equality atoms :   47 ( 335 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f219,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f100,f156,f158,f160,f194,f212,f214,f216,f218])).

fof(f218,plain,(
    ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f36,f203])).

fof(f203,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl4_21
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f34,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
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
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2))
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,X1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,X2))
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
              & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,X2))
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
            & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
            & v1_funct_1(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,sK2))
          & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X3) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,sK2))
        & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X3) )
   => ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
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
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                   => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).

fof(f216,plain,
    ( spl4_21
    | ~ spl4_22
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f215,f142,f205,f202])).

fof(f205,plain,
    ( spl4_22
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f142,plain,
    ( spl4_12
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f215,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_12 ),
    inference(resolution,[],[f143,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

% (12535)Refutation not found, incomplete strategy% (12535)------------------------------
% (12535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

% (12535)Termination reason: Refutation not found, incomplete strategy

% (12535)Memory used [KB]: 11001
% (12535)Time elapsed: 0.119 s
% (12535)------------------------------
% (12535)------------------------------
fof(f143,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f214,plain,
    ( ~ spl4_14
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f213,f154,f145,f148])).

fof(f148,plain,
    ( spl4_14
  <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f145,plain,
    ( spl4_13
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f154,plain,
    ( spl4_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f213,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl4_16 ),
    inference(resolution,[],[f155,f46])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f154])).

fof(f212,plain,(
    spl4_22 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl4_22 ),
    inference(subsumption_resolution,[],[f38,f208])).

fof(f208,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_22 ),
    inference(resolution,[],[f206,f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f206,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f205])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f194,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f46,f152])).

fof(f152,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl4_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f160,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl4_14 ),
    inference(subsumption_resolution,[],[f45,f149])).

fof(f149,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f45,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f158,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f44,f146])).

fof(f146,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f156,plain,
    ( spl4_12
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | spl4_16
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f140,f92,f154,f151,f148,f145,f142])).

fof(f92,plain,
    ( spl4_5
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl4_5 ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f114,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

fof(f114,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f105,f82])).

fof(f82,plain,(
    sK3 = k7_relat_1(sK3,u1_struct_0(sK1)) ),
    inference(global_subsumption,[],[f63,f81])).

fof(f81,plain,
    ( sK3 = k7_relat_1(sK3,u1_struct_0(sK1))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f62,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f62,plain,(
    v4_relat_1(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[],[f46,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f63,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f46,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f105,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK1)))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f98,f93])).

fof(f93,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f98,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f48,f85])).

fof(f85,plain,(
    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f84,f43])).

fof(f43,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0)) ) ),
    inference(forward_demodulation,[],[f64,f65])).

fof(f65,plain,(
    ! [X1] : k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1) = k7_relat_1(sK3,X1) ),
    inference(global_subsumption,[],[f44,f61])).

fof(f61,plain,(
    ! [X1] :
      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1) = k7_relat_1(sK3,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f46,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f64,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(global_subsumption,[],[f36,f37,f38,f39,f40,f41,f44,f45,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f46,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f41,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f40,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f41,f95])).

fof(f95,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_4 ),
    inference(resolution,[],[f90,f50])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f90,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_4
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f94,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f87,f92,f89])).

fof(f87,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | u1_struct_0(sK2) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f53,f47])).

fof(f47,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (12526)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.49  % (12543)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.50  % (12528)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (12535)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (12530)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (12528)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (12545)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (12538)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.21/0.52  % (12526)Refutation not found, incomplete strategy% (12526)------------------------------
% 1.21/0.52  % (12526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (12526)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (12526)Memory used [KB]: 2046
% 1.21/0.52  % (12526)Time elapsed: 0.103 s
% 1.21/0.52  % (12526)------------------------------
% 1.21/0.52  % (12526)------------------------------
% 1.21/0.52  % (12538)Refutation not found, incomplete strategy% (12538)------------------------------
% 1.21/0.52  % (12538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (12538)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (12538)Memory used [KB]: 10874
% 1.21/0.52  % (12538)Time elapsed: 0.116 s
% 1.21/0.52  % (12538)------------------------------
% 1.21/0.52  % (12538)------------------------------
% 1.21/0.52  % SZS output start Proof for theBenchmark
% 1.21/0.52  fof(f219,plain,(
% 1.21/0.52    $false),
% 1.21/0.52    inference(avatar_sat_refutation,[],[f94,f100,f156,f158,f160,f194,f212,f214,f216,f218])).
% 1.21/0.52  fof(f218,plain,(
% 1.21/0.52    ~spl4_21),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f217])).
% 1.21/0.52  fof(f217,plain,(
% 1.21/0.52    $false | ~spl4_21),
% 1.21/0.52    inference(subsumption_resolution,[],[f36,f203])).
% 1.21/0.52  fof(f203,plain,(
% 1.21/0.52    v2_struct_0(sK0) | ~spl4_21),
% 1.21/0.52    inference(avatar_component_clause,[],[f202])).
% 1.21/0.52  fof(f202,plain,(
% 1.21/0.52    spl4_21 <=> v2_struct_0(sK0)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.21/0.52  fof(f36,plain,(
% 1.21/0.52    ~v2_struct_0(sK0)),
% 1.21/0.52    inference(cnf_transformation,[],[f35])).
% 1.21/0.52  fof(f35,plain,(
% 1.21/0.52    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f34,f33,f32,f31])).
% 1.21/0.52  fof(f31,plain,(
% 1.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.21/0.52    introduced(choice_axiom,[])).
% 1.21/0.52  fof(f32,plain,(
% 1.21/0.52    ? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.21/0.52    introduced(choice_axiom,[])).
% 1.21/0.52  fof(f33,plain,(
% 1.21/0.52    ? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 1.21/0.52    introduced(choice_axiom,[])).
% 1.21/0.52  fof(f34,plain,(
% 1.21/0.52    ? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3))),
% 1.21/0.52    introduced(choice_axiom,[])).
% 1.21/0.52  fof(f15,plain,(
% 1.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.21/0.52    inference(flattening,[],[f14])).
% 1.21/0.52  fof(f14,plain,(
% 1.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.21/0.52    inference(ennf_transformation,[],[f12])).
% 1.21/0.52  fof(f12,negated_conjecture,(
% 1.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 1.21/0.52    inference(negated_conjecture,[],[f11])).
% 1.21/0.52  fof(f11,conjecture,(
% 1.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).
% 1.21/0.52  fof(f216,plain,(
% 1.21/0.52    spl4_21 | ~spl4_22 | ~spl4_12),
% 1.21/0.52    inference(avatar_split_clause,[],[f215,f142,f205,f202])).
% 1.21/0.52  fof(f205,plain,(
% 1.21/0.52    spl4_22 <=> l1_struct_0(sK0)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.21/0.52  fof(f142,plain,(
% 1.21/0.52    spl4_12 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.21/0.52  fof(f215,plain,(
% 1.21/0.52    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl4_12),
% 1.21/0.52    inference(resolution,[],[f143,f51])).
% 1.21/0.52  fof(f51,plain,(
% 1.21/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f19])).
% 1.21/0.52  fof(f19,plain,(
% 1.21/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.21/0.52    inference(flattening,[],[f18])).
% 1.21/0.52  fof(f18,plain,(
% 1.21/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.21/0.52    inference(ennf_transformation,[],[f7])).
% 1.21/0.52  % (12535)Refutation not found, incomplete strategy% (12535)------------------------------
% 1.21/0.52  % (12535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  fof(f7,axiom,(
% 1.21/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.21/0.52  % (12535)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (12535)Memory used [KB]: 11001
% 1.21/0.52  % (12535)Time elapsed: 0.119 s
% 1.21/0.52  % (12535)------------------------------
% 1.21/0.52  % (12535)------------------------------
% 1.21/0.52  fof(f143,plain,(
% 1.21/0.52    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_12),
% 1.21/0.52    inference(avatar_component_clause,[],[f142])).
% 1.21/0.52  fof(f214,plain,(
% 1.21/0.52    ~spl4_14 | ~spl4_13 | ~spl4_16),
% 1.21/0.52    inference(avatar_split_clause,[],[f213,f154,f145,f148])).
% 1.21/0.52  fof(f148,plain,(
% 1.21/0.52    spl4_14 <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.21/0.52  fof(f145,plain,(
% 1.21/0.52    spl4_13 <=> v1_funct_1(sK3)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.21/0.52  fof(f154,plain,(
% 1.21/0.52    spl4_16 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.21/0.52  fof(f213,plain,(
% 1.21/0.52    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl4_16),
% 1.21/0.52    inference(resolution,[],[f155,f46])).
% 1.21/0.52  fof(f46,plain,(
% 1.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.21/0.52    inference(cnf_transformation,[],[f35])).
% 1.21/0.52  fof(f155,plain,(
% 1.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))) ) | ~spl4_16),
% 1.21/0.52    inference(avatar_component_clause,[],[f154])).
% 1.21/0.52  fof(f212,plain,(
% 1.21/0.52    spl4_22),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f211])).
% 1.21/0.52  fof(f211,plain,(
% 1.21/0.52    $false | spl4_22),
% 1.21/0.52    inference(subsumption_resolution,[],[f38,f208])).
% 1.21/0.52  fof(f208,plain,(
% 1.21/0.52    ~l1_pre_topc(sK0) | spl4_22),
% 1.21/0.52    inference(resolution,[],[f206,f49])).
% 1.21/0.52  fof(f49,plain,(
% 1.21/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f16])).
% 1.21/0.52  fof(f16,plain,(
% 1.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.21/0.52    inference(ennf_transformation,[],[f5])).
% 1.21/0.52  fof(f5,axiom,(
% 1.21/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.21/0.52  fof(f206,plain,(
% 1.21/0.52    ~l1_struct_0(sK0) | spl4_22),
% 1.21/0.52    inference(avatar_component_clause,[],[f205])).
% 1.21/0.52  fof(f38,plain,(
% 1.21/0.52    l1_pre_topc(sK0)),
% 1.21/0.52    inference(cnf_transformation,[],[f35])).
% 1.21/0.52  fof(f194,plain,(
% 1.21/0.52    spl4_15),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f193])).
% 1.21/0.52  fof(f193,plain,(
% 1.21/0.52    $false | spl4_15),
% 1.21/0.52    inference(subsumption_resolution,[],[f46,f152])).
% 1.21/0.52  fof(f152,plain,(
% 1.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | spl4_15),
% 1.21/0.52    inference(avatar_component_clause,[],[f151])).
% 1.21/0.52  fof(f151,plain,(
% 1.21/0.52    spl4_15 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.21/0.52  fof(f160,plain,(
% 1.21/0.52    spl4_14),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f159])).
% 1.21/0.52  fof(f159,plain,(
% 1.21/0.52    $false | spl4_14),
% 1.21/0.52    inference(subsumption_resolution,[],[f45,f149])).
% 1.21/0.52  fof(f149,plain,(
% 1.21/0.52    ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | spl4_14),
% 1.21/0.52    inference(avatar_component_clause,[],[f148])).
% 1.21/0.52  fof(f45,plain,(
% 1.21/0.52    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.21/0.52    inference(cnf_transformation,[],[f35])).
% 1.21/0.52  fof(f158,plain,(
% 1.21/0.52    spl4_13),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f157])).
% 1.21/0.52  fof(f157,plain,(
% 1.21/0.52    $false | spl4_13),
% 1.21/0.52    inference(subsumption_resolution,[],[f44,f146])).
% 1.21/0.52  fof(f146,plain,(
% 1.21/0.52    ~v1_funct_1(sK3) | spl4_13),
% 1.21/0.52    inference(avatar_component_clause,[],[f145])).
% 1.21/0.52  fof(f44,plain,(
% 1.21/0.52    v1_funct_1(sK3)),
% 1.21/0.52    inference(cnf_transformation,[],[f35])).
% 1.21/0.52  fof(f156,plain,(
% 1.21/0.52    spl4_12 | ~spl4_13 | ~spl4_14 | ~spl4_15 | spl4_16 | ~spl4_5),
% 1.21/0.52    inference(avatar_split_clause,[],[f140,f92,f154,f151,f148,f145,f142])).
% 1.21/0.52  fof(f92,plain,(
% 1.21/0.52    spl4_5 <=> u1_struct_0(sK1) = u1_struct_0(sK2)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.21/0.52  fof(f140,plain,(
% 1.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0))) ) | ~spl4_5),
% 1.21/0.52    inference(duplicate_literal_removal,[],[f139])).
% 1.21/0.52  fof(f139,plain,(
% 1.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) ) | ~spl4_5),
% 1.21/0.52    inference(resolution,[],[f114,f59])).
% 1.21/0.52  fof(f59,plain,(
% 1.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f30])).
% 1.21/0.52  fof(f30,plain,(
% 1.21/0.52    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.21/0.52    inference(flattening,[],[f29])).
% 1.21/0.52  fof(f29,plain,(
% 1.21/0.52    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.21/0.52    inference(ennf_transformation,[],[f9])).
% 1.21/0.52  fof(f9,axiom,(
% 1.21/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).
% 1.21/0.52  fof(f114,plain,(
% 1.21/0.52    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | ~spl4_5),
% 1.21/0.52    inference(forward_demodulation,[],[f105,f82])).
% 1.21/0.52  fof(f82,plain,(
% 1.21/0.52    sK3 = k7_relat_1(sK3,u1_struct_0(sK1))),
% 1.21/0.52    inference(global_subsumption,[],[f63,f81])).
% 1.21/0.52  fof(f81,plain,(
% 1.21/0.52    sK3 = k7_relat_1(sK3,u1_struct_0(sK1)) | ~v1_relat_1(sK3)),
% 1.21/0.52    inference(resolution,[],[f62,f55])).
% 1.21/0.52  fof(f55,plain,(
% 1.21/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f24])).
% 1.21/0.52  fof(f24,plain,(
% 1.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.21/0.52    inference(flattening,[],[f23])).
% 1.21/0.52  fof(f23,plain,(
% 1.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.21/0.52    inference(ennf_transformation,[],[f1])).
% 1.21/0.52  fof(f1,axiom,(
% 1.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.21/0.52  fof(f62,plain,(
% 1.21/0.52    v4_relat_1(sK3,u1_struct_0(sK1))),
% 1.21/0.52    inference(resolution,[],[f46,f57])).
% 1.21/0.52  fof(f57,plain,(
% 1.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f26])).
% 1.21/0.52  fof(f26,plain,(
% 1.21/0.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.52    inference(ennf_transformation,[],[f13])).
% 1.21/0.52  fof(f13,plain,(
% 1.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.21/0.52    inference(pure_predicate_removal,[],[f3])).
% 1.21/0.52  fof(f3,axiom,(
% 1.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.21/0.52  fof(f63,plain,(
% 1.21/0.52    v1_relat_1(sK3)),
% 1.21/0.52    inference(resolution,[],[f46,f56])).
% 1.21/0.52  fof(f56,plain,(
% 1.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f25])).
% 1.21/0.52  fof(f25,plain,(
% 1.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.52    inference(ennf_transformation,[],[f2])).
% 1.21/0.52  fof(f2,axiom,(
% 1.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.21/0.52  fof(f105,plain,(
% 1.21/0.52    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK1))) | ~spl4_5),
% 1.21/0.52    inference(backward_demodulation,[],[f98,f93])).
% 1.21/0.52  fof(f93,plain,(
% 1.21/0.52    u1_struct_0(sK1) = u1_struct_0(sK2) | ~spl4_5),
% 1.21/0.52    inference(avatar_component_clause,[],[f92])).
% 1.21/0.52  fof(f98,plain,(
% 1.21/0.52    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k7_relat_1(sK3,u1_struct_0(sK2)))),
% 1.21/0.52    inference(backward_demodulation,[],[f48,f85])).
% 1.21/0.52  fof(f85,plain,(
% 1.21/0.52    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))),
% 1.21/0.52    inference(resolution,[],[f84,f43])).
% 1.21/0.52  fof(f43,plain,(
% 1.21/0.52    m1_pre_topc(sK2,sK1)),
% 1.21/0.52    inference(cnf_transformation,[],[f35])).
% 1.21/0.52  fof(f84,plain,(
% 1.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))) )),
% 1.21/0.52    inference(forward_demodulation,[],[f64,f65])).
% 1.21/0.52  fof(f65,plain,(
% 1.21/0.52    ( ! [X1] : (k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1) = k7_relat_1(sK3,X1)) )),
% 1.21/0.52    inference(global_subsumption,[],[f44,f61])).
% 1.21/0.52  fof(f61,plain,(
% 1.21/0.52    ( ! [X1] : (k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1) = k7_relat_1(sK3,X1) | ~v1_funct_1(sK3)) )),
% 1.21/0.52    inference(resolution,[],[f46,f58])).
% 1.21/0.52  fof(f58,plain,(
% 1.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f28])).
% 1.21/0.52  fof(f28,plain,(
% 1.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.21/0.52    inference(flattening,[],[f27])).
% 1.21/0.52  fof(f27,plain,(
% 1.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.21/0.52    inference(ennf_transformation,[],[f4])).
% 1.21/0.52  fof(f4,axiom,(
% 1.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.21/0.52  fof(f64,plain,(
% 1.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))) )),
% 1.21/0.52    inference(global_subsumption,[],[f36,f37,f38,f39,f40,f41,f44,f45,f60])).
% 1.21/0.52  fof(f60,plain,(
% 1.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.21/0.52    inference(resolution,[],[f46,f52])).
% 1.21/0.52  fof(f52,plain,(
% 1.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f21])).
% 1.21/0.52  fof(f21,plain,(
% 1.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.21/0.52    inference(flattening,[],[f20])).
% 1.21/0.52  fof(f20,plain,(
% 1.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.21/0.52    inference(ennf_transformation,[],[f10])).
% 1.21/0.52  fof(f10,axiom,(
% 1.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.21/0.52  fof(f41,plain,(
% 1.21/0.52    l1_pre_topc(sK1)),
% 1.21/0.52    inference(cnf_transformation,[],[f35])).
% 1.21/0.52  fof(f40,plain,(
% 1.21/0.52    v2_pre_topc(sK1)),
% 1.21/0.52    inference(cnf_transformation,[],[f35])).
% 1.21/0.52  fof(f39,plain,(
% 1.21/0.52    ~v2_struct_0(sK1)),
% 1.21/0.52    inference(cnf_transformation,[],[f35])).
% 1.21/0.52  fof(f37,plain,(
% 1.21/0.52    v2_pre_topc(sK0)),
% 1.21/0.52    inference(cnf_transformation,[],[f35])).
% 1.21/0.52  fof(f48,plain,(
% 1.21/0.52    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 1.21/0.52    inference(cnf_transformation,[],[f35])).
% 1.21/0.52  fof(f100,plain,(
% 1.21/0.52    spl4_4),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f99])).
% 1.21/0.52  fof(f99,plain,(
% 1.21/0.52    $false | spl4_4),
% 1.21/0.52    inference(subsumption_resolution,[],[f41,f95])).
% 1.21/0.52  fof(f95,plain,(
% 1.21/0.52    ~l1_pre_topc(sK1) | spl4_4),
% 1.21/0.52    inference(resolution,[],[f90,f50])).
% 1.21/0.52  fof(f50,plain,(
% 1.21/0.52    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f17])).
% 1.21/0.52  fof(f17,plain,(
% 1.21/0.52    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.21/0.52    inference(ennf_transformation,[],[f6])).
% 1.21/0.52  fof(f6,axiom,(
% 1.21/0.52    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.21/0.52  fof(f90,plain,(
% 1.21/0.52    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl4_4),
% 1.21/0.52    inference(avatar_component_clause,[],[f89])).
% 1.21/0.52  fof(f89,plain,(
% 1.21/0.52    spl4_4 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.21/0.52  fof(f94,plain,(
% 1.21/0.52    ~spl4_4 | spl4_5),
% 1.21/0.52    inference(avatar_split_clause,[],[f87,f92,f89])).
% 1.21/0.52  fof(f87,plain,(
% 1.21/0.52    u1_struct_0(sK1) = u1_struct_0(sK2) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.21/0.52    inference(equality_resolution,[],[f66])).
% 1.21/0.52  fof(f66,plain,(
% 1.21/0.52    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | u1_struct_0(sK2) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.21/0.52    inference(superposition,[],[f53,f47])).
% 1.21/0.52  fof(f47,plain,(
% 1.21/0.52    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.21/0.52    inference(cnf_transformation,[],[f35])).
% 1.21/0.52  fof(f53,plain,(
% 1.21/0.52    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.21/0.52    inference(cnf_transformation,[],[f22])).
% 1.21/0.52  fof(f22,plain,(
% 1.21/0.52    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.21/0.52    inference(ennf_transformation,[],[f8])).
% 1.21/0.52  fof(f8,axiom,(
% 1.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.21/0.52  % SZS output end Proof for theBenchmark
% 1.21/0.52  % (12528)------------------------------
% 1.21/0.52  % (12528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (12528)Termination reason: Refutation
% 1.21/0.52  
% 1.21/0.52  % (12528)Memory used [KB]: 10874
% 1.21/0.52  % (12528)Time elapsed: 0.105 s
% 1.21/0.52  % (12528)------------------------------
% 1.21/0.52  % (12528)------------------------------
% 1.21/0.53  % (12550)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.21/0.53  % (12520)Success in time 0.168 s
%------------------------------------------------------------------------------
