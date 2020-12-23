%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1285+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:38 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 398 expanded)
%              Number of leaves         :   40 ( 193 expanded)
%              Depth                    :   11
%              Number of atoms          :  645 (2263 expanded)
%              Number of equality atoms :   41 (  69 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f396,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f97,f98,f103,f108,f113,f118,f123,f151,f156,f166,f174,f211,f216,f221,f238,f244,f266,f321,f369,f382,f386,f389,f395])).

fof(f395,plain,
    ( sK2 != k1_tops_1(sK0,sK2)
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f389,plain,
    ( spl8_20
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f388,f180,f110,f100,f88,f184])).

fof(f184,plain,
    ( spl8_20
  <=> sK3 = k1_tops_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f88,plain,
    ( spl8_5
  <=> v3_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f100,plain,
    ( spl8_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f110,plain,
    ( spl8_9
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f180,plain,
    ( spl8_19
  <=> sP7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f388,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | sK3 = k1_tops_1(sK1,sK3)
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f387,f181])).

fof(f181,plain,
    ( sP7
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f180])).

fof(f387,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | sK3 = k1_tops_1(sK1,sK3)
    | ~ sP7
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f136,f112])).

fof(f112,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f136,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | sK3 = k1_tops_1(sK1,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ sP7
    | ~ spl8_7 ),
    inference(resolution,[],[f102,f68])).

fof(f68,plain,(
    ! [X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3
      | ~ l1_pre_topc(X1)
      | ~ sP7 ) ),
    inference(general_splitting,[],[f66,f67_D])).

fof(f67,plain,(
    ! [X0] :
      ( sP7
      | ~ v2_pre_topc(X0)
      | ~ sP6(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67_D])).

fof(f67_D,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ sP6(X0)
        | ~ l1_pre_topc(X0) )
  <=> ~ sP7 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP6(X0) ) ),
    inference(general_splitting,[],[f51,f65_D])).

fof(f65,plain,(
    ! [X2,X0] :
      ( sP6(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f65_D])).

fof(f65_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    <=> ~ sP6(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f102,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f386,plain,
    ( ~ spl8_2
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_19
    | spl8_30 ),
    inference(avatar_split_clause,[],[f385,f286,f180,f115,f105,f74])).

fof(f74,plain,
    ( spl8_2
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f105,plain,
    ( spl8_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f115,plain,
    ( spl8_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f286,plain,
    ( spl8_30
  <=> sK2 = k1_tops_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f385,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_19
    | spl8_30 ),
    inference(subsumption_resolution,[],[f384,f181])).

fof(f384,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ sP7
    | ~ spl8_8
    | ~ spl8_10
    | spl8_30 ),
    inference(subsumption_resolution,[],[f383,f117])).

fof(f117,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f383,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ sP7
    | ~ spl8_8
    | spl8_30 ),
    inference(subsumption_resolution,[],[f206,f288])).

fof(f288,plain,
    ( sK2 != k1_tops_1(sK0,sK2)
    | spl8_30 ),
    inference(avatar_component_clause,[],[f286])).

fof(f206,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | sK2 = k1_tops_1(sK0,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ sP7
    | ~ spl8_8 ),
    inference(resolution,[],[f107,f68])).

fof(f107,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f382,plain,
    ( spl8_2
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_24
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f381,f228,f218,f120,f115,f74])).

fof(f120,plain,
    ( spl8_11
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f218,plain,
    ( spl8_24
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f228,plain,
    ( spl8_26
  <=> sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f381,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_24
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f380,f122])).

fof(f122,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f380,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_10
    | ~ spl8_24
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f379,f117])).

fof(f379,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_24
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f360,f220])).

fof(f220,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f218])).

fof(f360,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_26 ),
    inference(superposition,[],[f50,f230])).

fof(f230,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f228])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f369,plain,
    ( spl8_3
    | ~ spl8_39
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f364,f228,f115,f105,f366,f78])).

fof(f78,plain,
    ( spl8_3
  <=> v4_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f366,plain,
    ( spl8_39
  <=> r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f364,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f363,f117])).

fof(f363,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_8
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f362,f107])).

fof(f362,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f357,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f357,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_26 ),
    inference(superposition,[],[f49,f230])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

fof(f321,plain,
    ( spl8_27
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f314,f184,f153,f148,f110,f100,f261])).

fof(f261,plain,
    ( spl8_27
  <=> r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f148,plain,
    ( spl8_14
  <=> r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f153,plain,
    ( spl8_15
  <=> m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f314,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_15
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f307,f186])).

fof(f186,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f184])).

fof(f307,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f112,f102,f150,f155,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f155,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f153])).

fof(f150,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f266,plain,
    ( ~ spl8_27
    | ~ spl8_17
    | spl8_18 ),
    inference(avatar_split_clause,[],[f265,f168,f163,f261])).

fof(f163,plain,
    ( spl8_17
  <=> r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f168,plain,
    ( spl8_18
  <=> sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f265,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ spl8_17
    | spl8_18 ),
    inference(subsumption_resolution,[],[f258,f170])).

fof(f170,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | spl8_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f258,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ spl8_17 ),
    inference(resolution,[],[f165,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f165,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f163])).

fof(f244,plain,
    ( ~ spl8_10
    | ~ spl8_11
    | spl8_19
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl8_10
    | ~ spl8_11
    | spl8_19
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f241,f210])).

fof(f210,plain,
    ( sP6(sK0)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl8_22
  <=> sP6(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f241,plain,
    ( ~ sP6(sK0)
    | ~ spl8_10
    | ~ spl8_11
    | spl8_19 ),
    inference(unit_resulting_resolution,[],[f117,f122,f182,f67])).

fof(f182,plain,
    ( ~ sP7
    | spl8_19 ),
    inference(avatar_component_clause,[],[f180])).

fof(f238,plain,
    ( spl8_26
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f237,f115,f105,f93,f228])).

fof(f93,plain,
    ( spl8_6
  <=> v6_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f237,plain,
    ( ~ v6_tops_1(sK2,sK0)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f203,f117])).

fof(f203,plain,
    ( ~ v6_tops_1(sK2,sK0)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f107,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

fof(f221,plain,
    ( spl8_24
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f197,f115,f105,f218])).

fof(f197,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f117,f107,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f216,plain,
    ( spl8_23
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f198,f115,f105,f213])).

fof(f213,plain,
    ( spl8_23
  <=> r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f198,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f117,f107,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f211,plain,
    ( spl8_22
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f202,f105,f208])).

fof(f202,plain,
    ( sP6(sK0)
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f107,f65])).

fof(f174,plain,
    ( ~ spl8_18
    | spl8_1
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f173,f110,f100,f70,f168])).

fof(f70,plain,
    ( spl8_1
  <=> v6_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f173,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f172,f112])).

fof(f172,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ l1_pre_topc(sK1)
    | spl8_1
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f134,f72])).

fof(f72,plain,
    ( ~ v6_tops_1(sK3,sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f134,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | v6_tops_1(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl8_7 ),
    inference(resolution,[],[f102,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | v6_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f166,plain,
    ( spl8_17
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f125,f110,f100,f83,f163])).

fof(f83,plain,
    ( spl8_4
  <=> v4_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f125,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f112,f85,f102,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f156,plain,
    ( spl8_15
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f127,f110,f100,f153])).

fof(f127,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f112,f102,f56])).

fof(f151,plain,
    ( spl8_14
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f128,f110,f100,f148])).

fof(f128,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f112,f102,f57])).

fof(f123,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f34,f120])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ( ( ~ v4_tops_1(sK2,sK0)
          | ~ v3_pre_topc(sK2,sK0) )
        & v6_tops_1(sK2,sK0) )
      | ( ~ v6_tops_1(sK3,sK1)
        & v4_tops_1(sK3,sK1)
        & v3_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v3_pre_topc(X2,X0) )
                        & v6_tops_1(X2,X0) )
                      | ( ~ v6_tops_1(X3,X1)
                        & v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK0)
                        | ~ v3_pre_topc(X2,sK0) )
                      & v6_tops_1(X2,sK0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,sK0)
                      | ~ v3_pre_topc(X2,sK0) )
                    & v6_tops_1(X2,sK0) )
                  | ( ~ v6_tops_1(X3,X1)
                    & v4_tops_1(X3,X1)
                    & v3_pre_topc(X3,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,sK0)
                    | ~ v3_pre_topc(X2,sK0) )
                  & v6_tops_1(X2,sK0) )
                | ( ~ v6_tops_1(X3,sK1)
                  & v4_tops_1(X3,sK1)
                  & v3_pre_topc(X3,sK1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(X2,sK0)
                  | ~ v3_pre_topc(X2,sK0) )
                & v6_tops_1(X2,sK0) )
              | ( ~ v6_tops_1(X3,sK1)
                & v4_tops_1(X3,sK1)
                & v3_pre_topc(X3,sK1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(sK2,sK0)
                | ~ v3_pre_topc(sK2,sK0) )
              & v6_tops_1(sK2,sK0) )
            | ( ~ v6_tops_1(X3,sK1)
              & v4_tops_1(X3,sK1)
              & v3_pre_topc(X3,sK1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ( ( ( ~ v4_tops_1(sK2,sK0)
              | ~ v3_pre_topc(sK2,sK0) )
            & v6_tops_1(sK2,sK0) )
          | ( ~ v6_tops_1(X3,sK1)
            & v4_tops_1(X3,sK1)
            & v3_pre_topc(X3,sK1) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ( ( ~ v4_tops_1(sK2,sK0)
            | ~ v3_pre_topc(sK2,sK0) )
          & v6_tops_1(sK2,sK0) )
        | ( ~ v6_tops_1(sK3,sK1)
          & v4_tops_1(sK3,sK1)
          & v3_pre_topc(sK3,sK1) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v6_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v3_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v3_pre_topc(X3,X1) )
                       => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v6_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v3_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) )
                     => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_tops_1)).

fof(f118,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f35,f115])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f113,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f36,f110])).

fof(f36,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f108,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f37,f105])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f103,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f38,f100])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f98,plain,
    ( spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f39,f93,f88])).

fof(f39,plain,
    ( v6_tops_1(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,
    ( spl8_4
    | spl8_6 ),
    inference(avatar_split_clause,[],[f40,f93,f83])).

fof(f40,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,
    ( ~ spl8_1
    | spl8_6 ),
    inference(avatar_split_clause,[],[f41,f93,f70])).

fof(f41,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,
    ( spl8_5
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f42,f78,f74,f88])).

fof(f42,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,
    ( spl8_4
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f43,f78,f74,f83])).

fof(f43,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f44,f78,f74,f70])).

fof(f44,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

%------------------------------------------------------------------------------
