%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 419 expanded)
%              Number of leaves         :   44 ( 202 expanded)
%              Depth                    :   10
%              Number of atoms          :  697 (2329 expanded)
%              Number of equality atoms :   48 (  77 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f720,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f109,f110,f115,f120,f125,f130,f135,f174,f205,f218,f220,f234,f243,f267,f272,f297,f301,f358,f368,f382,f389,f633,f645,f649,f719])).

fof(f719,plain,
    ( ~ spl8_5
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_15
    | ~ spl8_32
    | spl8_35 ),
    inference(avatar_contradiction_clause,[],[f718])).

fof(f718,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_15
    | ~ spl8_32
    | spl8_35 ),
    inference(subsumption_resolution,[],[f715,f355])).

fof(f355,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | spl8_35 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl8_35
  <=> r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f715,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_15
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f124,f102,f114,f173,f309,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f309,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl8_32
  <=> r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f173,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl8_15
  <=> m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f114,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl8_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f102,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl8_5
  <=> v3_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f124,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_9
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f649,plain,
    ( spl8_36
    | ~ spl8_10
    | ~ spl8_28
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f620,f284,f269,f127,f365])).

fof(f365,plain,
    ( spl8_36
  <=> sK2 = k1_tops_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f127,plain,
    ( spl8_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f269,plain,
    ( spl8_28
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f284,plain,
    ( spl8_31
  <=> sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f620,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl8_10
    | ~ spl8_28
    | ~ spl8_31 ),
    inference(forward_demodulation,[],[f596,f286])).

fof(f286,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f284])).

fof(f596,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2)))
    | ~ spl8_10
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f129,f271,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f271,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f269])).

fof(f129,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f645,plain,
    ( ~ spl8_4
    | spl8_32
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f644,f228,f122,f112,f307,f95])).

fof(f95,plain,
    ( spl8_4
  <=> v4_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f228,plain,
    ( spl8_24
  <=> sK3 = k1_tops_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f644,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ v4_tops_1(sK3,sK1)
    | ~ spl8_7
    | ~ spl8_9
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f643,f124])).

fof(f643,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ v4_tops_1(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl8_7
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f320,f114])).

fof(f320,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ v4_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl8_24 ),
    inference(superposition,[],[f56,f230])).

fof(f230,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f228])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(f633,plain,
    ( sK2 != k1_tops_1(sK0,sK2)
    | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f389,plain,
    ( spl8_38
    | ~ spl8_10
    | ~ spl8_28
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f384,f284,f269,f127,f386])).

fof(f386,plain,
    ( spl8_38
  <=> r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f384,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl8_10
    | ~ spl8_28
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f383,f129])).

fof(f383,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_28
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f372,f271])).

fof(f372,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_31 ),
    inference(superposition,[],[f66,f286])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f382,plain,
    ( spl8_3
    | ~ spl8_37
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f377,f284,f127,f117,f379,f90])).

fof(f90,plain,
    ( spl8_3
  <=> v4_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f379,plain,
    ( spl8_37
  <=> r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f117,plain,
    ( spl8_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f377,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f376,f129])).

fof(f376,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_8
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f375,f119])).

fof(f119,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f375,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f371,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f371,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_31 ),
    inference(superposition,[],[f57,f286])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f368,plain,
    ( ~ spl8_36
    | spl8_2
    | ~ spl8_8
    | spl8_25 ),
    inference(avatar_split_clause,[],[f362,f240,f117,f86,f365])).

fof(f86,plain,
    ( spl8_2
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f240,plain,
    ( spl8_25
  <=> sP4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f362,plain,
    ( sK2 != k1_tops_1(sK0,sK2)
    | spl8_2
    | ~ spl8_8
    | spl8_25 ),
    inference(unit_resulting_resolution,[],[f88,f119,f242,f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( sP4(X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f73_D])).

fof(f73_D,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_tops_1(X0,X2) != X2
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | v3_pre_topc(X2,X0) )
    <=> ~ sP4(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f242,plain,
    ( ~ sP4(sK0)
    | spl8_25 ),
    inference(avatar_component_clause,[],[f240])).

fof(f88,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f358,plain,
    ( ~ spl8_35
    | ~ spl8_21
    | spl8_22 ),
    inference(avatar_split_clause,[],[f357,f207,f202,f353])).

fof(f202,plain,
    ( spl8_21
  <=> r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f207,plain,
    ( spl8_22
  <=> sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f357,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ spl8_21
    | spl8_22 ),
    inference(subsumption_resolution,[],[f340,f209])).

fof(f209,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | spl8_22 ),
    inference(avatar_component_clause,[],[f207])).

fof(f340,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ spl8_21 ),
    inference(resolution,[],[f204,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f204,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f202])).

fof(f301,plain,
    ( ~ spl8_10
    | ~ spl8_11
    | spl8_23
    | ~ spl8_27 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | ~ spl8_10
    | ~ spl8_11
    | spl8_23
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f298,f266])).

fof(f266,plain,
    ( sP6(sK0)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl8_27
  <=> sP6(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f298,plain,
    ( ~ sP6(sK0)
    | ~ spl8_10
    | ~ spl8_11
    | spl8_23 ),
    inference(unit_resulting_resolution,[],[f129,f134,f226,f79])).

fof(f79,plain,(
    ! [X0] :
      ( sP7
      | ~ v2_pre_topc(X0)
      | ~ sP6(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79_D])).

fof(f79_D,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ sP6(X0)
        | ~ l1_pre_topc(X0) )
  <=> ~ sP7 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f226,plain,
    ( ~ sP7
    | spl8_23 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl8_23
  <=> sP7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f134,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl8_11
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f297,plain,
    ( spl8_31
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f296,f127,f117,f105,f284])).

fof(f105,plain,
    ( spl8_6
  <=> v6_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f296,plain,
    ( ~ v6_tops_1(sK2,sK0)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f253,f129])).

% (12050)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f253,plain,
    ( ~ v6_tops_1(sK2,sK0)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f119,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

fof(f272,plain,
    ( spl8_28
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f247,f127,f117,f269])).

fof(f247,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f129,f119,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f267,plain,
    ( spl8_27
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f249,f117,f264])).

fof(f249,plain,
    ( sP6(sK0)
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f119,f77])).

fof(f77,plain,(
    ! [X2,X0] :
      ( sP6(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f77_D])).

fof(f77_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    <=> ~ sP6(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f243,plain,
    ( ~ spl8_25
    | ~ spl8_10
    | ~ spl8_11
    | spl8_14 ),
    inference(avatar_split_clause,[],[f237,f166,f132,f127,f240])).

fof(f166,plain,
    ( spl8_14
  <=> sP5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f237,plain,
    ( ~ sP4(sK0)
    | ~ spl8_10
    | ~ spl8_11
    | spl8_14 ),
    inference(unit_resulting_resolution,[],[f129,f134,f168,f75])).

fof(f75,plain,(
    ! [X0] :
      ( sP5
      | ~ v2_pre_topc(X0)
      | ~ sP4(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f75_D])).

fof(f75_D,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ sP4(X0)
        | ~ l1_pre_topc(X0) )
  <=> ~ sP5 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f168,plain,
    ( ~ sP5
    | spl8_14 ),
    inference(avatar_component_clause,[],[f166])).

fof(f234,plain,
    ( ~ spl8_23
    | spl8_24
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f233,f122,f112,f100,f228,f224])).

fof(f233,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | sK3 = k1_tops_1(sK1,sK3)
    | ~ sP7
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f153,f124])).

fof(f153,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | sK3 = k1_tops_1(sK1,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ sP7
    | ~ spl8_7 ),
    inference(resolution,[],[f114,f80])).

fof(f80,plain,(
    ! [X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3
      | ~ l1_pre_topc(X1)
      | ~ sP7 ) ),
    inference(general_splitting,[],[f78,f79_D])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP6(X0) ) ),
    inference(general_splitting,[],[f60,f77_D])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f220,plain,
    ( ~ spl8_14
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f219,f122,f112,f166])).

fof(f219,plain,
    ( ~ sP5
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f152,f124])).

fof(f152,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ sP5
    | ~ spl8_7 ),
    inference(resolution,[],[f114,f76])).

fof(f76,plain,(
    ! [X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ sP5 ) ),
    inference(general_splitting,[],[f74,f75_D])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP4(X0) ) ),
    inference(general_splitting,[],[f61,f73_D])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f218,plain,
    ( ~ spl8_22
    | spl8_1
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f217,f122,f112,f82,f207])).

fof(f82,plain,
    ( spl8_1
  <=> v6_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f217,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | spl8_1
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f216,f124])).

fof(f216,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ l1_pre_topc(sK1)
    | spl8_1
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f151,f84])).

fof(f84,plain,
    ( ~ v6_tops_1(sK3,sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f151,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | v6_tops_1(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl8_7 ),
    inference(resolution,[],[f114,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | v6_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f205,plain,
    ( spl8_21
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f137,f122,f112,f95,f202])).

fof(f137,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f124,f97,f114,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f95])).

% (12046)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (12047)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (12062)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (12061)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% (12053)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% (12070)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (12063)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f174,plain,
    ( spl8_15
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f144,f122,f112,f171])).

fof(f144,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f124,f114,f67])).

fof(f135,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f42,f132])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f34,f33,f32,f31])).

fof(f31,plain,
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

fof(f32,plain,
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

fof(f33,plain,
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

fof(f34,plain,
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

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

fof(f130,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f43,f127])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f125,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f44,f122])).

fof(f44,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f120,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f45,f117])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f115,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f46,f112])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f110,plain,
    ( spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f47,f105,f100])).

fof(f47,plain,
    ( v6_tops_1(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f109,plain,
    ( spl8_4
    | spl8_6 ),
    inference(avatar_split_clause,[],[f48,f105,f95])).

fof(f48,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f108,plain,
    ( ~ spl8_1
    | spl8_6 ),
    inference(avatar_split_clause,[],[f49,f105,f82])).

fof(f49,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f103,plain,
    ( spl8_5
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f50,f90,f86,f100])).

fof(f50,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f98,plain,
    ( spl8_4
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f51,f90,f86,f95])).

fof(f51,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f52,f90,f86,f82])).

fof(f52,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (12066)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.46  % (12058)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.48  % (12049)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (12056)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  % (12048)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (12068)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (12067)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (12055)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (12060)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (12069)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (12057)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (12059)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (12051)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (12052)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (12065)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (12059)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f720,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f109,f110,f115,f120,f125,f130,f135,f174,f205,f218,f220,f234,f243,f267,f272,f297,f301,f358,f368,f382,f389,f633,f645,f649,f719])).
% 0.21/0.51  fof(f719,plain,(
% 0.21/0.51    ~spl8_5 | ~spl8_7 | ~spl8_9 | ~spl8_15 | ~spl8_32 | spl8_35),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f718])).
% 0.21/0.51  fof(f718,plain,(
% 0.21/0.51    $false | (~spl8_5 | ~spl8_7 | ~spl8_9 | ~spl8_15 | ~spl8_32 | spl8_35)),
% 0.21/0.51    inference(subsumption_resolution,[],[f715,f355])).
% 0.21/0.51  fof(f355,plain,(
% 0.21/0.51    ~r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | spl8_35),
% 0.21/0.51    inference(avatar_component_clause,[],[f353])).
% 0.21/0.51  fof(f353,plain,(
% 0.21/0.51    spl8_35 <=> r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.21/0.51  fof(f715,plain,(
% 0.21/0.51    r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | (~spl8_5 | ~spl8_7 | ~spl8_9 | ~spl8_15 | ~spl8_32)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f124,f102,f114,f173,f309,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 0.21/0.51  fof(f309,plain,(
% 0.21/0.51    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | ~spl8_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f307])).
% 0.21/0.51  fof(f307,plain,(
% 0.21/0.51    spl8_32 <=> r1_tarski(sK3,k2_pre_topc(sK1,sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl8_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f171])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    spl8_15 <=> m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl8_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl8_7 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    v3_pre_topc(sK3,sK1) | ~spl8_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl8_5 <=> v3_pre_topc(sK3,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    l1_pre_topc(sK1) | ~spl8_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    spl8_9 <=> l1_pre_topc(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.51  fof(f649,plain,(
% 0.21/0.51    spl8_36 | ~spl8_10 | ~spl8_28 | ~spl8_31),
% 0.21/0.51    inference(avatar_split_clause,[],[f620,f284,f269,f127,f365])).
% 0.21/0.51  fof(f365,plain,(
% 0.21/0.51    spl8_36 <=> sK2 = k1_tops_1(sK0,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    spl8_10 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    spl8_28 <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    spl8_31 <=> sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.21/0.51  fof(f620,plain,(
% 0.21/0.51    sK2 = k1_tops_1(sK0,sK2) | (~spl8_10 | ~spl8_28 | ~spl8_31)),
% 0.21/0.51    inference(forward_demodulation,[],[f596,f286])).
% 0.21/0.51  fof(f286,plain,(
% 0.21/0.51    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~spl8_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f284])).
% 0.21/0.51  fof(f596,plain,(
% 0.21/0.51    k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) | (~spl8_10 | ~spl8_28)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f129,f271,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f269])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl8_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f127])).
% 0.21/0.51  fof(f645,plain,(
% 0.21/0.51    ~spl8_4 | spl8_32 | ~spl8_7 | ~spl8_9 | ~spl8_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f644,f228,f122,f112,f307,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl8_4 <=> v4_tops_1(sK3,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    spl8_24 <=> sK3 = k1_tops_1(sK1,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.21/0.51  fof(f644,plain,(
% 0.21/0.51    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | ~v4_tops_1(sK3,sK1) | (~spl8_7 | ~spl8_9 | ~spl8_24)),
% 0.21/0.51    inference(subsumption_resolution,[],[f643,f124])).
% 0.21/0.51  fof(f643,plain,(
% 0.21/0.51    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | ~v4_tops_1(sK3,sK1) | ~l1_pre_topc(sK1) | (~spl8_7 | ~spl8_24)),
% 0.21/0.51    inference(subsumption_resolution,[],[f320,f114])).
% 0.21/0.51  fof(f320,plain,(
% 0.21/0.51    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | ~v4_tops_1(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~spl8_24),
% 0.21/0.51    inference(superposition,[],[f56,f230])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    sK3 = k1_tops_1(sK1,sK3) | ~spl8_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f228])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).
% 0.21/0.51  fof(f633,plain,(
% 0.21/0.51    sK2 != k1_tops_1(sK0,sK2) | r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | ~r1_tarski(sK2,k2_pre_topc(sK0,sK2))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f389,plain,(
% 0.21/0.51    spl8_38 | ~spl8_10 | ~spl8_28 | ~spl8_31),
% 0.21/0.51    inference(avatar_split_clause,[],[f384,f284,f269,f127,f386])).
% 0.21/0.51  fof(f386,plain,(
% 0.21/0.51    spl8_38 <=> r1_tarski(sK2,k2_pre_topc(sK0,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 0.21/0.51  fof(f384,plain,(
% 0.21/0.51    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | (~spl8_10 | ~spl8_28 | ~spl8_31)),
% 0.21/0.51    inference(subsumption_resolution,[],[f383,f129])).
% 0.21/0.51  fof(f383,plain,(
% 0.21/0.51    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0) | (~spl8_28 | ~spl8_31)),
% 0.21/0.51    inference(subsumption_resolution,[],[f372,f271])).
% 0.21/0.51  fof(f372,plain,(
% 0.21/0.51    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl8_31),
% 0.21/0.51    inference(superposition,[],[f66,f286])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.51  fof(f382,plain,(
% 0.21/0.51    spl8_3 | ~spl8_37 | ~spl8_8 | ~spl8_10 | ~spl8_31),
% 0.21/0.51    inference(avatar_split_clause,[],[f377,f284,f127,f117,f379,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl8_3 <=> v4_tops_1(sK2,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.51  fof(f379,plain,(
% 0.21/0.51    spl8_37 <=> r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl8_8 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.51  fof(f377,plain,(
% 0.21/0.51    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | (~spl8_8 | ~spl8_10 | ~spl8_31)),
% 0.21/0.51    inference(subsumption_resolution,[],[f376,f129])).
% 0.21/0.51  fof(f376,plain,(
% 0.21/0.51    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | ~l1_pre_topc(sK0) | (~spl8_8 | ~spl8_31)),
% 0.21/0.51    inference(subsumption_resolution,[],[f375,f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f117])).
% 0.21/0.51  fof(f375,plain,(
% 0.21/0.51    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl8_31),
% 0.21/0.51    inference(subsumption_resolution,[],[f371,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f371,plain,(
% 0.21/0.51    ~r1_tarski(sK2,sK2) | ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl8_31),
% 0.21/0.51    inference(superposition,[],[f57,f286])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f368,plain,(
% 0.21/0.51    ~spl8_36 | spl8_2 | ~spl8_8 | spl8_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f362,f240,f117,f86,f365])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl8_2 <=> v3_pre_topc(sK2,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    spl8_25 <=> sP4(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.51  fof(f362,plain,(
% 0.21/0.51    sK2 != k1_tops_1(sK0,sK2) | (spl8_2 | ~spl8_8 | spl8_25)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f88,f119,f242,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X2,X0] : (sP4(X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f73_D])).
% 0.21/0.51  fof(f73_D,plain,(
% 0.21/0.51    ( ! [X0] : (( ! [X2] : (k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0)) ) <=> ~sP4(X0)) )),
% 0.21/0.51    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    ~sP4(sK0) | spl8_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f240])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ~v3_pre_topc(sK2,sK0) | spl8_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f86])).
% 0.21/0.51  fof(f358,plain,(
% 0.21/0.51    ~spl8_35 | ~spl8_21 | spl8_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f357,f207,f202,f353])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    spl8_21 <=> r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    spl8_22 <=> sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.51  fof(f357,plain,(
% 0.21/0.51    ~r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | (~spl8_21 | spl8_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f340,f209])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | spl8_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f207])).
% 0.21/0.51  fof(f340,plain,(
% 0.21/0.51    ~r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~spl8_21),
% 0.21/0.51    inference(resolution,[],[f204,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~spl8_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f202])).
% 0.21/0.51  fof(f301,plain,(
% 0.21/0.51    ~spl8_10 | ~spl8_11 | spl8_23 | ~spl8_27),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f300])).
% 0.21/0.51  fof(f300,plain,(
% 0.21/0.51    $false | (~spl8_10 | ~spl8_11 | spl8_23 | ~spl8_27)),
% 0.21/0.51    inference(subsumption_resolution,[],[f298,f266])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    sP6(sK0) | ~spl8_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f264])).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    spl8_27 <=> sP6(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.51  fof(f298,plain,(
% 0.21/0.51    ~sP6(sK0) | (~spl8_10 | ~spl8_11 | spl8_23)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f129,f134,f226,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X0] : (sP7 | ~v2_pre_topc(X0) | ~sP6(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f79_D])).
% 0.21/0.51  fof(f79_D,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_pre_topc(X0) | ~sP6(X0) | ~l1_pre_topc(X0)) ) <=> ~sP7),
% 0.21/0.51    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    ~sP7 | spl8_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f224])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    spl8_23 <=> sP7),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    v2_pre_topc(sK0) | ~spl8_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f132])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    spl8_11 <=> v2_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    spl8_31 | ~spl8_6 | ~spl8_8 | ~spl8_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f296,f127,f117,f105,f284])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl8_6 <=> v6_tops_1(sK2,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.51  fof(f296,plain,(
% 0.21/0.51    ~v6_tops_1(sK2,sK0) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | (~spl8_8 | ~spl8_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f253,f129])).
% 0.21/0.51  % (12050)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    ~v6_tops_1(sK2,sK0) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0) | ~spl8_8),
% 0.21/0.51    inference(resolution,[],[f119,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    spl8_28 | ~spl8_8 | ~spl8_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f247,f127,f117,f269])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl8_8 | ~spl8_10)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f129,f119,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.51  fof(f267,plain,(
% 0.21/0.51    spl8_27 | ~spl8_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f249,f117,f264])).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    sP6(sK0) | ~spl8_8),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f119,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X2,X0] : (sP6(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f77_D])).
% 0.21/0.51  fof(f77_D,plain,(
% 0.21/0.51    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) <=> ~sP6(X0)) )),
% 0.21/0.51    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    ~spl8_25 | ~spl8_10 | ~spl8_11 | spl8_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f237,f166,f132,f127,f240])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    spl8_14 <=> sP5),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    ~sP4(sK0) | (~spl8_10 | ~spl8_11 | spl8_14)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f129,f134,f168,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0] : (sP5 | ~v2_pre_topc(X0) | ~sP4(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f75_D])).
% 0.21/0.51  fof(f75_D,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_pre_topc(X0) | ~sP4(X0) | ~l1_pre_topc(X0)) ) <=> ~sP5),
% 0.21/0.51    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ~sP5 | spl8_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f166])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    ~spl8_23 | spl8_24 | ~spl8_5 | ~spl8_7 | ~spl8_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f233,f122,f112,f100,f228,f224])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    ~v3_pre_topc(sK3,sK1) | sK3 = k1_tops_1(sK1,sK3) | ~sP7 | (~spl8_7 | ~spl8_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f153,f124])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ~v3_pre_topc(sK3,sK1) | sK3 = k1_tops_1(sK1,sK3) | ~l1_pre_topc(sK1) | ~sP7 | ~spl8_7),
% 0.21/0.51    inference(resolution,[],[f114,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~sP7) )),
% 0.21/0.51    inference(general_splitting,[],[f78,f79_D])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP6(X0)) )),
% 0.21/0.51    inference(general_splitting,[],[f60,f77_D])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    ~spl8_14 | ~spl8_7 | ~spl8_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f219,f122,f112,f166])).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    ~sP5 | (~spl8_7 | ~spl8_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f152,f124])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ~l1_pre_topc(sK1) | ~sP5 | ~spl8_7),
% 0.21/0.51    inference(resolution,[],[f114,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~sP5) )),
% 0.21/0.51    inference(general_splitting,[],[f74,f75_D])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP4(X0)) )),
% 0.21/0.51    inference(general_splitting,[],[f61,f73_D])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    ~spl8_22 | spl8_1 | ~spl8_7 | ~spl8_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f217,f122,f112,f82,f207])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl8_1 <=> v6_tops_1(sK3,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | (spl8_1 | ~spl8_7 | ~spl8_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f216,f124])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~l1_pre_topc(sK1) | (spl8_1 | ~spl8_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f151,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ~v6_tops_1(sK3,sK1) | spl8_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f82])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | v6_tops_1(sK3,sK1) | ~l1_pre_topc(sK1) | ~spl8_7),
% 0.21/0.51    inference(resolution,[],[f114,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | v6_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    spl8_21 | ~spl8_4 | ~spl8_7 | ~spl8_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f137,f122,f112,f95,f202])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | (~spl8_4 | ~spl8_7 | ~spl8_9)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f124,f97,f114,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    v4_tops_1(sK3,sK1) | ~spl8_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f95])).
% 0.21/0.51  % (12046)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (12047)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (12062)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (12061)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (12053)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (12070)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (12063)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    spl8_15 | ~spl8_7 | ~spl8_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f144,f122,f112,f171])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl8_7 | ~spl8_9)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f124,f114,f67])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    spl8_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f42,f132])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    v2_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ((((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f34,f33,f32,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f12])).
% 0.21/0.54  fof(f12,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    spl8_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f43,f127])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    l1_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    spl8_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f44,f122])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    l1_pre_topc(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    spl8_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f45,f117])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    spl8_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f46,f112])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    spl8_5 | spl8_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f47,f105,f100])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    v6_tops_1(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    spl8_4 | spl8_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f48,f105,f95])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ~spl8_1 | spl8_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f49,f105,f82])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    v6_tops_1(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    spl8_5 | ~spl8_2 | ~spl8_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f50,f90,f86,f100])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    spl8_4 | ~spl8_2 | ~spl8_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f51,f90,f86,f95])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f52,f90,f86,f82])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (12059)------------------------------
% 0.21/0.54  % (12059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12059)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (12059)Memory used [KB]: 6652
% 0.21/0.54  % (12059)Time elapsed: 0.114 s
% 0.21/0.54  % (12059)------------------------------
% 0.21/0.54  % (12059)------------------------------
% 0.21/0.54  % (12045)Success in time 0.188 s
%------------------------------------------------------------------------------
