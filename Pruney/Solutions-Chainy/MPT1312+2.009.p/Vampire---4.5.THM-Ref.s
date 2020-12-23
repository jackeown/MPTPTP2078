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
% DateTime   : Thu Dec  3 13:13:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 218 expanded)
%              Number of leaves         :   33 (  95 expanded)
%              Depth                    :    9
%              Number of atoms          :  320 ( 581 expanded)
%              Number of equality atoms :   20 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f779,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f72,f80,f86,f95,f105,f108,f114,f125,f135,f144,f157,f348,f665,f678,f776,f778])).

fof(f778,plain,
    ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(k2_struct_0(sK1))
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f776,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_15
    | spl3_65 ),
    inference(avatar_contradiction_clause,[],[f775])).

fof(f775,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_15
    | spl3_65 ),
    inference(subsumption_resolution,[],[f774,f156])).

fof(f156,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl3_15
  <=> m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f774,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_11
    | spl3_65 ),
    inference(forward_demodulation,[],[f771,f113])).

fof(f113,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_11
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f771,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl3_3
    | ~ spl3_4
    | spl3_65 ),
    inference(unit_resulting_resolution,[],[f63,f58,f677,f393])).

fof(f393,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f390,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f390,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f36,f32])).

fof(f32,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f677,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_65 ),
    inference(avatar_component_clause,[],[f675])).

fof(f675,plain,
    ( spl3_65
  <=> m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f58,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_3
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f63,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f678,plain,
    ( ~ spl3_65
    | spl3_62 ),
    inference(avatar_split_clause,[],[f666,f658,f675])).

fof(f658,plain,
    ( spl3_62
  <=> r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f666,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_62 ),
    inference(unit_resulting_resolution,[],[f660,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f660,plain,
    ( ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))
    | spl3_62 ),
    inference(avatar_component_clause,[],[f658])).

fof(f665,plain,
    ( ~ spl3_62
    | spl3_63
    | spl3_39 ),
    inference(avatar_split_clause,[],[f642,f345,f662,f658])).

fof(f662,plain,
    ( spl3_63
  <=> k1_zfmisc_1(k2_struct_0(sK0)) = k1_zfmisc_1(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f345,plain,
    ( spl3_39
  <=> r2_xboole_0(k1_zfmisc_1(k2_struct_0(sK1)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f642,plain,
    ( k1_zfmisc_1(k2_struct_0(sK0)) = k1_zfmisc_1(k2_struct_0(sK1))
    | ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))
    | spl3_39 ),
    inference(resolution,[],[f245,f347])).

fof(f347,plain,
    ( ~ r2_xboole_0(k1_zfmisc_1(k2_struct_0(sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_39 ),
    inference(avatar_component_clause,[],[f345])).

fof(f245,plain,(
    ! [X2,X3] :
      ( r2_xboole_0(k1_zfmisc_1(X2),k1_zfmisc_1(X3))
      | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f40,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f348,plain,
    ( ~ spl3_39
    | ~ spl3_12
    | spl3_14 ),
    inference(avatar_split_clause,[],[f326,f140,f121,f345])).

fof(f121,plain,
    ( spl3_12
  <=> r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f140,plain,
    ( spl3_14
  <=> r2_xboole_0(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f326,plain,
    ( ~ r2_xboole_0(k1_zfmisc_1(k2_struct_0(sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_12
    | spl3_14 ),
    inference(unit_resulting_resolution,[],[f142,f123,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X2)
      | r2_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l58_xboole_1)).

fof(f123,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f142,plain,
    ( ~ r2_xboole_0(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f140])).

fof(f157,plain,
    ( spl3_15
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f152,f111,f88,f154])).

fof(f88,plain,
    ( spl3_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f152,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f146,f113])).

fof(f146,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f89,f33])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f89,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f144,plain,
    ( ~ spl3_14
    | spl3_13 ),
    inference(avatar_split_clause,[],[f138,f131,f140])).

fof(f131,plain,
    ( spl3_13
  <=> r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f138,plain,
    ( ~ r2_xboole_0(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_13 ),
    inference(resolution,[],[f133,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f133,plain,
    ( ~ r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f135,plain,
    ( ~ spl3_13
    | spl3_7 ),
    inference(avatar_split_clause,[],[f128,f83,f131])).

fof(f83,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f128,plain,
    ( ~ r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_7 ),
    inference(resolution,[],[f42,f85])).

fof(f85,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f125,plain,
    ( spl3_12
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f119,f92,f121])).

fof(f92,plain,
    ( spl3_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f119,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ spl3_9 ),
    inference(resolution,[],[f41,f94])).

fof(f94,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK1))))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f114,plain,
    ( spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f109,f88,f111])).

fof(f109,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f89,f32])).

fof(f108,plain,
    ( spl3_8
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f106,f102])).

fof(f102,plain,
    ( l1_pre_topc(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl3_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f106,plain,
    ( ~ l1_pre_topc(sK1)
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f90,f34])).

fof(f90,plain,
    ( ~ l1_struct_0(sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f105,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f104,f61,f56,f100])).

fof(f104,plain,
    ( l1_pre_topc(sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f98,f63])).

fof(f98,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f35,f58])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f95,plain,
    ( ~ spl3_8
    | spl3_9
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f75,f51,f92,f88])).

fof(f51,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

% (6283)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f53,f32])).

fof(f53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f86,plain,
    ( ~ spl3_7
    | spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f81,f68,f46,f83])).

fof(f46,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f68,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f81,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | spl3_1
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f74,f70])).

fof(f70,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f74,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ l1_struct_0(sK0)
    | spl3_1 ),
    inference(superposition,[],[f48,f32])).

fof(f48,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f80,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f73,f68,f77])).

fof(f77,plain,
    ( spl3_6
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f73,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f70,f32])).

fof(f72,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f66,f61,f68])).

fof(f66,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f34,f63])).

fof(f64,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
   => ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

fof(f59,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f29,f56])).

fof(f29,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f51])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f31,f46])).

fof(f31,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:05:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (6291)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (6292)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (6300)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (6300)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f779,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f72,f80,f86,f95,f105,f108,f114,f125,f135,f144,f157,f348,f665,f678,f776,f778])).
% 0.21/0.51  fof(f778,plain,(
% 0.21/0.51    k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(k2_struct_0(sK1)) | u1_struct_0(sK1) != k2_struct_0(sK1) | u1_struct_0(sK0) != k2_struct_0(sK0) | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK1))))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f776,plain,(
% 0.21/0.51    ~spl3_3 | ~spl3_4 | ~spl3_11 | ~spl3_15 | spl3_65),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f775])).
% 0.21/0.51  fof(f775,plain,(
% 0.21/0.51    $false | (~spl3_3 | ~spl3_4 | ~spl3_11 | ~spl3_15 | spl3_65)),
% 0.21/0.51    inference(subsumption_resolution,[],[f774,f156])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) | ~spl3_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f154])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    spl3_15 <=> m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.51  fof(f774,plain,(
% 0.21/0.51    ~m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) | (~spl3_3 | ~spl3_4 | ~spl3_11 | spl3_65)),
% 0.21/0.51    inference(forward_demodulation,[],[f771,f113])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl3_11 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.51  fof(f771,plain,(
% 0.21/0.51    ~m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl3_3 | ~spl3_4 | spl3_65)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f63,f58,f677,f393])).
% 0.21/0.51  fof(f393,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f390,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.51  fof(f390,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.51    inference(superposition,[],[f36,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.51  fof(f677,plain,(
% 0.21/0.51    ~m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_65),
% 0.21/0.51    inference(avatar_component_clause,[],[f675])).
% 0.21/0.51  fof(f675,plain,(
% 0.21/0.51    spl3_65 <=> m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    m1_pre_topc(sK1,sK0) | ~spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    spl3_3 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl3_4 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f678,plain,(
% 0.21/0.51    ~spl3_65 | spl3_62),
% 0.21/0.51    inference(avatar_split_clause,[],[f666,f658,f675])).
% 0.21/0.51  fof(f658,plain,(
% 0.21/0.51    spl3_62 <=> r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.21/0.51  fof(f666,plain,(
% 0.21/0.51    ~m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_62),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f660,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f660,plain,(
% 0.21/0.51    ~r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0)) | spl3_62),
% 0.21/0.51    inference(avatar_component_clause,[],[f658])).
% 0.21/0.51  fof(f665,plain,(
% 0.21/0.51    ~spl3_62 | spl3_63 | spl3_39),
% 0.21/0.51    inference(avatar_split_clause,[],[f642,f345,f662,f658])).
% 0.21/0.51  fof(f662,plain,(
% 0.21/0.51    spl3_63 <=> k1_zfmisc_1(k2_struct_0(sK0)) = k1_zfmisc_1(k2_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 0.21/0.51  fof(f345,plain,(
% 0.21/0.51    spl3_39 <=> r2_xboole_0(k1_zfmisc_1(k2_struct_0(sK1)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.51  fof(f642,plain,(
% 0.21/0.51    k1_zfmisc_1(k2_struct_0(sK0)) = k1_zfmisc_1(k2_struct_0(sK1)) | ~r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0)) | spl3_39),
% 0.21/0.51    inference(resolution,[],[f245,f347])).
% 0.21/0.51  fof(f347,plain,(
% 0.21/0.51    ~r2_xboole_0(k1_zfmisc_1(k2_struct_0(sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_39),
% 0.21/0.51    inference(avatar_component_clause,[],[f345])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r2_xboole_0(k1_zfmisc_1(X2),k1_zfmisc_1(X3)) | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) | ~r1_tarski(X2,X3)) )),
% 0.21/0.51    inference(resolution,[],[f40,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.51  fof(f348,plain,(
% 0.21/0.51    ~spl3_39 | ~spl3_12 | spl3_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f326,f140,f121,f345])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl3_12 <=> r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    spl3_14 <=> r2_xboole_0(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.51  fof(f326,plain,(
% 0.21/0.51    ~r2_xboole_0(k1_zfmisc_1(k2_struct_0(sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_12 | spl3_14)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f142,f123,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X2) | r2_xboole_0(X0,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l58_xboole_1)).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK1))) | ~spl3_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f121])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ~r2_xboole_0(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | spl3_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f140])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    spl3_15 | ~spl3_8 | ~spl3_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f152,f111,f88,f154])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl3_8 <=> l1_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) | (~spl3_8 | ~spl3_11)),
% 0.21/0.51    inference(forward_demodulation,[],[f146,f113])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl3_8),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f89,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    l1_struct_0(sK1) | ~spl3_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f88])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ~spl3_14 | spl3_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f138,f131,f140])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl3_13 <=> r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ~r2_xboole_0(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | spl3_13),
% 0.21/0.51    inference(resolution,[],[f133,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ~r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | spl3_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f131])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ~spl3_13 | spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f128,f83,f131])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ~r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | spl3_7),
% 0.21/0.51    inference(resolution,[],[f42,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | spl3_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f83])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    spl3_12 | ~spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f119,f92,f121])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl3_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK1))) | ~spl3_9),
% 0.21/0.51    inference(resolution,[],[f41,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK1)))) | ~spl3_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f92])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl3_11 | ~spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f109,f88,f111])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_8),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f89,f32])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    spl3_8 | ~spl3_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f107])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    $false | (spl3_8 | ~spl3_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f106,f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    l1_pre_topc(sK1) | ~spl3_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl3_10 <=> l1_pre_topc(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ~l1_pre_topc(sK1) | spl3_8),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f90,f34])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ~l1_struct_0(sK1) | spl3_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f88])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl3_10 | ~spl3_3 | ~spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f104,f61,f56,f100])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    l1_pre_topc(sK1) | (~spl3_3 | ~spl3_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f98,f63])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 0.21/0.51    inference(resolution,[],[f35,f58])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ~spl3_8 | spl3_9 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f75,f51,f92,f88])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  % (6283)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~spl3_2),
% 0.21/0.51    inference(superposition,[],[f53,f32])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f51])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~spl3_7 | spl3_1 | ~spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f81,f68,f46,f83])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl3_5 <=> l1_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | (spl3_1 | ~spl3_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f74,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    l1_struct_0(sK0) | ~spl3_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f68])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) | ~l1_struct_0(sK0) | spl3_1),
% 0.21/0.51    inference(superposition,[],[f48,f32])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f46])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl3_6 | ~spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f73,f68,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl3_6 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f70,f32])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl3_5 | ~spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f66,f61,f68])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    l1_struct_0(sK0) | ~spl3_4),
% 0.21/0.51    inference(resolution,[],[f34,f63])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f28,f61])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ((~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,sK0)) => (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_pre_topc(sK1,sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) => (~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f56])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    m1_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f51])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ~spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f31,f46])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (6300)------------------------------
% 0.21/0.51  % (6300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6300)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (6300)Memory used [KB]: 11129
% 0.21/0.51  % (6300)Time elapsed: 0.085 s
% 0.21/0.51  % (6300)------------------------------
% 0.21/0.51  % (6300)------------------------------
% 0.21/0.51  % (6275)Success in time 0.154 s
%------------------------------------------------------------------------------
