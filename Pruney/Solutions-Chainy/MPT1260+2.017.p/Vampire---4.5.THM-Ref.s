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
% DateTime   : Thu Dec  3 13:11:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 372 expanded)
%              Number of leaves         :   44 ( 142 expanded)
%              Depth                    :   16
%              Number of atoms          :  530 (1081 expanded)
%              Number of equality atoms :  104 ( 264 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1054,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f110,f115,f124,f127,f233,f243,f267,f323,f328,f492,f511,f535,f545,f717,f770,f943,f965,f980,f1023,f1030,f1052,f1053])).

fof(f1053,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1052,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_30
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f1031,f1027,f542,f112,f107])).

fof(f107,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f112,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f542,plain,
    ( spl3_30
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f1027,plain,
    ( spl3_48
  <=> sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f1031,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_48 ),
    inference(superposition,[],[f1029,f347])).

fof(f347,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k6_subset_1(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k6_subset_1(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f94,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f68,f82])).

fof(f82,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1029,plain,
    ( sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f1027])).

fof(f1030,plain,
    ( ~ spl3_21
    | spl3_48
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f1024,f1020,f1027,f299])).

fof(f299,plain,
    ( spl3_21
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f1020,plain,
    ( spl3_47
  <=> sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f1024,plain,
    ( sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_47 ),
    inference(superposition,[],[f1022,f94])).

fof(f1022,plain,
    ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f1020])).

fof(f1023,plain,
    ( ~ spl3_21
    | ~ spl3_14
    | spl3_47
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f998,f977,f1020,f264,f299])).

fof(f264,plain,
    ( spl3_14
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f977,plain,
    ( spl3_43
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f998,plain,
    ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_43 ),
    inference(superposition,[],[f394,f979])).

fof(f979,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f977])).

fof(f394,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k7_subset_1(X0,k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(condensation,[],[f393])).

fof(f393,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X1) = k7_subset_1(X0,k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f84,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f980,plain,
    ( ~ spl3_21
    | spl3_43
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f968,f303,f977,f299])).

fof(f303,plain,
    ( spl3_22
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f968,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_22 ),
    inference(superposition,[],[f85,f304])).

fof(f304,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f303])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f965,plain,
    ( ~ spl3_21
    | spl3_22
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f776,f230,f303,f299])).

fof(f230,plain,
    ( spl3_11
  <=> k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f776,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_11 ),
    inference(superposition,[],[f232,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k6_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f81,f82])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f232,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f230])).

fof(f943,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_23 ),
    inference(avatar_contradiction_clause,[],[f930])).

fof(f930,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_23 ),
    inference(unit_resulting_resolution,[],[f109,f322,f114,f746])).

fof(f746,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
      | r1_tarski(X6,k2_pre_topc(X7,X6))
      | ~ l1_pre_topc(X7) ) ),
    inference(superposition,[],[f144,f376])).

fof(f376,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f74,f373])).

fof(f373,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f372])).

fof(f372,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f87,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f144,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(trivial_inequality_removal,[],[f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X0,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f96,f98])).

fof(f98,plain,(
    ! [X0,X1] : k1_xboole_0 = k6_subset_1(X0,k2_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f83,f82])).

fof(f83,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f79,f82])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f114,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f322,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl3_23
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f109,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f770,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f734,f542,f121,f112,f107])).

fof(f121,plain,
    ( spl3_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f734,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_30 ),
    inference(superposition,[],[f70,f544])).

fof(f544,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f542])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f717,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_29 ),
    inference(avatar_contradiction_clause,[],[f704])).

fof(f704,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_29 ),
    inference(unit_resulting_resolution,[],[f109,f540,f114,f696])).

fof(f696,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9)))
      | r1_tarski(k1_tops_1(X9,X8),X8)
      | ~ l1_pre_topc(X9) ) ),
    inference(superposition,[],[f130,f347])).

fof(f130,plain,(
    ! [X2,X1] : r1_tarski(k6_subset_1(X1,X2),X1) ),
    inference(resolution,[],[f88,f93])).

fof(f93,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f540,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f538])).

fof(f538,plain,
    ( spl3_29
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f545,plain,
    ( ~ spl3_29
    | spl3_30
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f536,f504,f542,f538])).

fof(f504,plain,
    ( spl3_27
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f536,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_27 ),
    inference(resolution,[],[f506,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f506,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f504])).

fof(f535,plain,(
    spl3_28 ),
    inference(avatar_contradiction_clause,[],[f530])).

fof(f530,plain,
    ( $false
    | spl3_28 ),
    inference(unit_resulting_resolution,[],[f455,f510,f88])).

fof(f510,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl3_28
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f455,plain,(
    ! [X6] : m1_subset_1(X6,k1_zfmisc_1(X6)) ),
    inference(global_subsumption,[],[f138,f446])).

fof(f446,plain,(
    ! [X6] :
      ( m1_subset_1(X6,k1_zfmisc_1(X6))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X6)) ) ),
    inference(superposition,[],[f86,f438])).

fof(f438,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(global_subsumption,[],[f138,f433])).

fof(f433,plain,(
    ! [X0] :
      ( k3_subset_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f425,f175])).

fof(f175,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X1,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f86,f88])).

fof(f425,plain,(
    ! [X1] :
      ( ~ r1_tarski(k3_subset_1(X1,k1_xboole_0),X1)
      | k3_subset_1(X1,k1_xboole_0) = X1 ) ),
    inference(resolution,[],[f423,f92])).

fof(f423,plain,(
    ! [X0] : r1_tarski(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(global_subsumption,[],[f138,f422])).

fof(f422,plain,(
    ! [X0] :
      ( r1_tarski(X0,k3_subset_1(X0,k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f384])).

fof(f384,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | r1_tarski(X0,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(global_subsumption,[],[f86,f377])).

fof(f377,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | r1_tarski(X0,k3_subset_1(X0,X1))
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f203,f85])).

fof(f203,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k3_subset_1(X2,X3)
      | r1_tarski(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f96,f97])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f138,plain,(
    ! [X2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2)) ),
    inference(superposition,[],[f93,f98])).

fof(f511,plain,
    ( ~ spl3_4
    | spl3_27
    | ~ spl3_28
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f501,f490,f112,f508,f504,f117])).

fof(f117,plain,
    ( spl3_4
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f490,plain,
    ( spl3_26
  <=> ! [X20] :
        ( ~ r1_tarski(X20,sK1)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X20,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X20,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f501,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_26 ),
    inference(resolution,[],[f491,f114])).

fof(f491,plain,
    ( ! [X20] :
        ( ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X20,sK1)
        | r1_tarski(X20,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X20,sK0) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f490])).

fof(f492,plain,
    ( ~ spl3_2
    | spl3_26
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f484,f112,f490,f107])).

fof(f484,plain,
    ( ! [X20] :
        ( ~ r1_tarski(X20,sK1)
        | ~ v3_pre_topc(X20,sK0)
        | r1_tarski(X20,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f77,f114])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f328,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_24
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f314,f112,f325,f107,f102])).

fof(f102,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f325,plain,
    ( spl3_24
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f314,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f76,f114])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f323,plain,
    ( ~ spl3_23
    | spl3_21 ),
    inference(avatar_split_clause,[],[f318,f299,f320])).

fof(f318,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl3_21 ),
    inference(resolution,[],[f301,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f301,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f299])).

fof(f267,plain,
    ( spl3_14
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f255,f230,f264])).

fof(f255,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_11 ),
    inference(superposition,[],[f93,f232])).

fof(f243,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f109,f114,f228,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f228,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl3_10
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f233,plain,
    ( ~ spl3_10
    | spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f223,f121,f230,f226])).

fof(f223,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(superposition,[],[f94,f123])).

fof(f123,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f127,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f126,f121,f117])).

fof(f126,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f125])).

fof(f125,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f67,f123])).

fof(f67,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f53,f55,f54])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f124,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f66,f121,f117])).

fof(f66,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f115,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f65,f112])).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f110,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f64,f107])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f105,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f63,f102])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:21:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (16984)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (16965)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (16978)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (16974)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (16964)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (16966)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (16963)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (16973)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (16988)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (16975)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (16971)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (16983)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (16962)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (16976)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (16977)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (16981)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (16967)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (16987)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (16982)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (16961)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (16990)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (16970)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (16980)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (16986)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (16985)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (16989)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (16979)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (16969)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (16972)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (16968)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (16971)Refutation not found, incomplete strategy% (16971)------------------------------
% 0.20/0.55  % (16971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (16971)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (16971)Memory used [KB]: 11001
% 0.20/0.55  % (16971)Time elapsed: 0.146 s
% 0.20/0.55  % (16971)------------------------------
% 0.20/0.55  % (16971)------------------------------
% 0.20/0.55  % (16977)Refutation not found, incomplete strategy% (16977)------------------------------
% 0.20/0.55  % (16977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (16977)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (16977)Memory used [KB]: 10746
% 0.20/0.55  % (16977)Time elapsed: 0.132 s
% 0.20/0.55  % (16977)------------------------------
% 0.20/0.55  % (16977)------------------------------
% 0.20/0.56  % (16989)Refutation not found, incomplete strategy% (16989)------------------------------
% 0.20/0.56  % (16989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (16989)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (16989)Memory used [KB]: 11001
% 0.20/0.56  % (16989)Time elapsed: 0.143 s
% 0.20/0.56  % (16989)------------------------------
% 0.20/0.56  % (16989)------------------------------
% 0.20/0.58  % (16984)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f1054,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(avatar_sat_refutation,[],[f105,f110,f115,f124,f127,f233,f243,f267,f323,f328,f492,f511,f535,f545,f717,f770,f943,f965,f980,f1023,f1030,f1052,f1053])).
% 0.20/0.58  fof(f1053,plain,(
% 0.20/0.58    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.20/0.58    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.58  fof(f1052,plain,(
% 0.20/0.58    ~spl3_2 | ~spl3_3 | spl3_30 | ~spl3_48),
% 0.20/0.58    inference(avatar_split_clause,[],[f1031,f1027,f542,f112,f107])).
% 0.20/0.58  fof(f107,plain,(
% 0.20/0.58    spl3_2 <=> l1_pre_topc(sK0)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.58  fof(f112,plain,(
% 0.20/0.58    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.58  fof(f542,plain,(
% 0.20/0.58    spl3_30 <=> sK1 = k1_tops_1(sK0,sK1)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.58  fof(f1027,plain,(
% 0.20/0.58    spl3_48 <=> sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.20/0.58  fof(f1031,plain,(
% 0.20/0.58    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_48),
% 0.20/0.58    inference(superposition,[],[f1029,f347])).
% 0.20/0.58  fof(f347,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k6_subset_1(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f346])).
% 0.20/0.58  fof(f346,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k6_subset_1(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(superposition,[],[f94,f71])).
% 0.20/0.58  fof(f71,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f35])).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f27])).
% 0.20/0.58  fof(f27,axiom,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 0.20/0.58  fof(f94,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f68,f82])).
% 0.20/0.58  fof(f82,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f15])).
% 0.20/0.58  fof(f15,axiom,(
% 0.20/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f32])).
% 0.20/0.58  fof(f32,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f16])).
% 0.20/0.58  fof(f16,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.20/0.58  fof(f1029,plain,(
% 0.20/0.58    sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl3_48),
% 0.20/0.58    inference(avatar_component_clause,[],[f1027])).
% 0.20/0.58  fof(f1030,plain,(
% 0.20/0.58    ~spl3_21 | spl3_48 | ~spl3_47),
% 0.20/0.58    inference(avatar_split_clause,[],[f1024,f1020,f1027,f299])).
% 0.20/0.58  fof(f299,plain,(
% 0.20/0.58    spl3_21 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.58  fof(f1020,plain,(
% 0.20/0.58    spl3_47 <=> sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.20/0.58  fof(f1024,plain,(
% 0.20/0.58    sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_47),
% 0.20/0.58    inference(superposition,[],[f1022,f94])).
% 0.20/0.58  fof(f1022,plain,(
% 0.20/0.58    sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | ~spl3_47),
% 0.20/0.58    inference(avatar_component_clause,[],[f1020])).
% 0.20/0.58  fof(f1023,plain,(
% 0.20/0.58    ~spl3_21 | ~spl3_14 | spl3_47 | ~spl3_43),
% 0.20/0.58    inference(avatar_split_clause,[],[f998,f977,f1020,f264,f299])).
% 0.20/0.58  fof(f264,plain,(
% 0.20/0.58    spl3_14 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.58  fof(f977,plain,(
% 0.20/0.58    spl3_43 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.20/0.58  fof(f998,plain,(
% 0.20/0.58    sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_43),
% 0.20/0.58    inference(superposition,[],[f394,f979])).
% 0.20/0.58  fof(f979,plain,(
% 0.20/0.58    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl3_43),
% 0.20/0.58    inference(avatar_component_clause,[],[f977])).
% 0.20/0.58  fof(f394,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k7_subset_1(X0,k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(condensation,[],[f393])).
% 0.20/0.58  fof(f393,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k3_subset_1(X0,X1) = k7_subset_1(X0,k3_subset_1(X0,X1),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(superposition,[],[f84,f69])).
% 0.20/0.58  fof(f69,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f33])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f17])).
% 0.20/0.58  fof(f17,axiom,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 0.20/0.58  fof(f84,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f47])).
% 0.20/0.58  fof(f47,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f11])).
% 0.20/0.58  fof(f11,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 0.20/0.58  fof(f980,plain,(
% 0.20/0.58    ~spl3_21 | spl3_43 | ~spl3_22),
% 0.20/0.58    inference(avatar_split_clause,[],[f968,f303,f977,f299])).
% 0.20/0.58  fof(f303,plain,(
% 0.20/0.58    spl3_22 <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.58  fof(f968,plain,(
% 0.20/0.58    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_22),
% 0.20/0.58    inference(superposition,[],[f85,f304])).
% 0.20/0.58  fof(f304,plain,(
% 0.20/0.58    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl3_22),
% 0.20/0.58    inference(avatar_component_clause,[],[f303])).
% 0.20/0.58  fof(f85,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f48])).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f12])).
% 0.20/0.58  fof(f12,axiom,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.58  fof(f965,plain,(
% 0.20/0.58    ~spl3_21 | spl3_22 | ~spl3_11),
% 0.20/0.58    inference(avatar_split_clause,[],[f776,f230,f303,f299])).
% 0.20/0.58  fof(f230,plain,(
% 0.20/0.58    spl3_11 <=> k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.58  fof(f776,plain,(
% 0.20/0.58    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_11),
% 0.20/0.58    inference(superposition,[],[f232,f97])).
% 0.20/0.58  fof(f97,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k6_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f81,f82])).
% 0.20/0.58  fof(f81,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f46])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.58  fof(f232,plain,(
% 0.20/0.58    k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl3_11),
% 0.20/0.58    inference(avatar_component_clause,[],[f230])).
% 0.20/0.58  fof(f943,plain,(
% 0.20/0.58    ~spl3_2 | ~spl3_3 | spl3_23),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f930])).
% 0.20/0.58  fof(f930,plain,(
% 0.20/0.58    $false | (~spl3_2 | ~spl3_3 | spl3_23)),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f109,f322,f114,f746])).
% 0.20/0.58  fof(f746,plain,(
% 0.20/0.58    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7))) | r1_tarski(X6,k2_pre_topc(X7,X6)) | ~l1_pre_topc(X7)) )),
% 0.20/0.58    inference(superposition,[],[f144,f376])).
% 0.20/0.58  fof(f376,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(global_subsumption,[],[f74,f373])).
% 0.20/0.58  fof(f373,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f372])).
% 0.20/0.58  fof(f372,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(superposition,[],[f87,f73])).
% 0.20/0.58  fof(f73,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f38])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f26])).
% 0.20/0.58  fof(f26,axiom,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.20/0.58  fof(f87,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f51])).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.58    inference(flattening,[],[f50])).
% 0.20/0.58  fof(f50,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.58    inference(ennf_transformation,[],[f14])).
% 0.20/0.58  fof(f14,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.58  fof(f74,plain,(
% 0.20/0.58    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(flattening,[],[f39])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f21])).
% 0.20/0.58  fof(f21,axiom,(
% 0.20/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.20/0.58  fof(f144,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f142])).
% 0.20/0.58  fof(f142,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.58    inference(superposition,[],[f96,f98])).
% 0.20/0.58  fof(f98,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f83,f82])).
% 0.20/0.58  fof(f83,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.58  fof(f96,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f79,f82])).
% 0.20/0.58  fof(f79,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f59])).
% 0.20/0.58  fof(f59,plain,(
% 0.20/0.58    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.58    inference(nnf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.58  fof(f114,plain,(
% 0.20/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.20/0.58    inference(avatar_component_clause,[],[f112])).
% 0.20/0.58  fof(f322,plain,(
% 0.20/0.58    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl3_23),
% 0.20/0.58    inference(avatar_component_clause,[],[f320])).
% 0.20/0.58  fof(f320,plain,(
% 0.20/0.58    spl3_23 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.58  fof(f109,plain,(
% 0.20/0.58    l1_pre_topc(sK0) | ~spl3_2),
% 0.20/0.58    inference(avatar_component_clause,[],[f107])).
% 0.20/0.58  fof(f770,plain,(
% 0.20/0.58    ~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_30),
% 0.20/0.58    inference(avatar_split_clause,[],[f734,f542,f121,f112,f107])).
% 0.20/0.58  fof(f121,plain,(
% 0.20/0.58    spl3_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.58  fof(f734,plain,(
% 0.20/0.58    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_30),
% 0.20/0.58    inference(superposition,[],[f70,f544])).
% 0.20/0.58  fof(f544,plain,(
% 0.20/0.58    sK1 = k1_tops_1(sK0,sK1) | ~spl3_30),
% 0.20/0.58    inference(avatar_component_clause,[],[f542])).
% 0.20/0.58  fof(f70,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f23])).
% 0.20/0.58  fof(f23,axiom,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.20/0.58  fof(f717,plain,(
% 0.20/0.58    ~spl3_2 | ~spl3_3 | spl3_29),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f704])).
% 0.20/0.58  fof(f704,plain,(
% 0.20/0.58    $false | (~spl3_2 | ~spl3_3 | spl3_29)),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f109,f540,f114,f696])).
% 0.20/0.58  fof(f696,plain,(
% 0.20/0.58    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9))) | r1_tarski(k1_tops_1(X9,X8),X8) | ~l1_pre_topc(X9)) )),
% 0.20/0.58    inference(superposition,[],[f130,f347])).
% 0.20/0.58  fof(f130,plain,(
% 0.20/0.58    ( ! [X2,X1] : (r1_tarski(k6_subset_1(X1,X2),X1)) )),
% 0.20/0.58    inference(resolution,[],[f88,f93])).
% 0.20/0.58  fof(f93,plain,(
% 0.20/0.58    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f9])).
% 0.20/0.58  fof(f9,axiom,(
% 0.20/0.58    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f60])).
% 0.20/0.58  fof(f60,plain,(
% 0.20/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.58    inference(nnf_transformation,[],[f19])).
% 0.20/0.58  fof(f19,axiom,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.58  fof(f540,plain,(
% 0.20/0.58    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | spl3_29),
% 0.20/0.58    inference(avatar_component_clause,[],[f538])).
% 0.20/0.58  fof(f538,plain,(
% 0.20/0.58    spl3_29 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.58  fof(f545,plain,(
% 0.20/0.58    ~spl3_29 | spl3_30 | ~spl3_27),
% 0.20/0.58    inference(avatar_split_clause,[],[f536,f504,f542,f538])).
% 0.20/0.58  fof(f504,plain,(
% 0.20/0.58    spl3_27 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.58  fof(f536,plain,(
% 0.20/0.58    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_27),
% 0.20/0.58    inference(resolution,[],[f506,f92])).
% 0.20/0.58  fof(f92,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f62])).
% 0.20/0.58  fof(f62,plain,(
% 0.20/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.58    inference(flattening,[],[f61])).
% 0.20/0.58  fof(f61,plain,(
% 0.20/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.58    inference(nnf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.58  fof(f506,plain,(
% 0.20/0.58    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl3_27),
% 0.20/0.58    inference(avatar_component_clause,[],[f504])).
% 0.20/0.58  fof(f535,plain,(
% 0.20/0.58    spl3_28),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f530])).
% 0.20/0.58  fof(f530,plain,(
% 0.20/0.58    $false | spl3_28),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f455,f510,f88])).
% 0.20/0.58  fof(f510,plain,(
% 0.20/0.58    ~r1_tarski(sK1,sK1) | spl3_28),
% 0.20/0.58    inference(avatar_component_clause,[],[f508])).
% 0.20/0.58  fof(f508,plain,(
% 0.20/0.58    spl3_28 <=> r1_tarski(sK1,sK1)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.58  fof(f455,plain,(
% 0.20/0.58    ( ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X6))) )),
% 0.20/0.58    inference(global_subsumption,[],[f138,f446])).
% 0.20/0.58  fof(f446,plain,(
% 0.20/0.58    ( ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X6)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X6))) )),
% 0.20/0.58    inference(superposition,[],[f86,f438])).
% 0.20/0.58  fof(f438,plain,(
% 0.20/0.58    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.58    inference(global_subsumption,[],[f138,f433])).
% 0.20/0.58  fof(f433,plain,(
% 0.20/0.58    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(resolution,[],[f425,f175])).
% 0.20/0.58  fof(f175,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X1,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.58    inference(resolution,[],[f86,f88])).
% 0.20/0.58  fof(f425,plain,(
% 0.20/0.58    ( ! [X1] : (~r1_tarski(k3_subset_1(X1,k1_xboole_0),X1) | k3_subset_1(X1,k1_xboole_0) = X1) )),
% 0.20/0.58    inference(resolution,[],[f423,f92])).
% 0.20/0.58  fof(f423,plain,(
% 0.20/0.58    ( ! [X0] : (r1_tarski(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 0.20/0.58    inference(global_subsumption,[],[f138,f422])).
% 0.20/0.58  fof(f422,plain,(
% 0.20/0.58    ( ! [X0] : (r1_tarski(X0,k3_subset_1(X0,k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(equality_resolution,[],[f384])).
% 0.20/0.59  fof(f384,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_xboole_0 != X1 | r1_tarski(X0,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.59    inference(global_subsumption,[],[f86,f377])).
% 0.20/0.59  fof(f377,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_xboole_0 != X1 | r1_tarski(X0,k3_subset_1(X0,X1)) | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.59    inference(superposition,[],[f203,f85])).
% 0.20/0.59  fof(f203,plain,(
% 0.20/0.59    ( ! [X2,X3] : (k1_xboole_0 != k3_subset_1(X2,X3) | r1_tarski(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 0.20/0.59    inference(superposition,[],[f96,f97])).
% 0.20/0.59  fof(f86,plain,(
% 0.20/0.59    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f49])).
% 0.20/0.59  fof(f49,plain,(
% 0.20/0.59    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f8])).
% 0.20/0.59  fof(f8,axiom,(
% 0.20/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.59  fof(f138,plain,(
% 0.20/0.59    ( ! [X2] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))) )),
% 0.20/0.59    inference(superposition,[],[f93,f98])).
% 0.20/0.59  fof(f511,plain,(
% 0.20/0.59    ~spl3_4 | spl3_27 | ~spl3_28 | ~spl3_3 | ~spl3_26),
% 0.20/0.59    inference(avatar_split_clause,[],[f501,f490,f112,f508,f504,f117])).
% 0.20/0.59  fof(f117,plain,(
% 0.20/0.59    spl3_4 <=> v3_pre_topc(sK1,sK0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.59  fof(f490,plain,(
% 0.20/0.59    spl3_26 <=> ! [X20] : (~r1_tarski(X20,sK1) | ~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X20,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X20,sK0))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.59  fof(f501,plain,(
% 0.20/0.59    ~r1_tarski(sK1,sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0) | (~spl3_3 | ~spl3_26)),
% 0.20/0.59    inference(resolution,[],[f491,f114])).
% 0.20/0.59  fof(f491,plain,(
% 0.20/0.59    ( ! [X20] : (~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X20,sK1) | r1_tarski(X20,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X20,sK0)) ) | ~spl3_26),
% 0.20/0.59    inference(avatar_component_clause,[],[f490])).
% 0.20/0.59  fof(f492,plain,(
% 0.20/0.59    ~spl3_2 | spl3_26 | ~spl3_3),
% 0.20/0.59    inference(avatar_split_clause,[],[f484,f112,f490,f107])).
% 0.20/0.59  fof(f484,plain,(
% 0.20/0.59    ( ! [X20] : (~r1_tarski(X20,sK1) | ~v3_pre_topc(X20,sK0) | r1_tarski(X20,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_3),
% 0.20/0.59    inference(resolution,[],[f77,f114])).
% 0.20/0.59  fof(f77,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f45])).
% 0.20/0.59  fof(f45,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.59    inference(flattening,[],[f44])).
% 0.20/0.59  fof(f44,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f24])).
% 0.20/0.59  fof(f24,axiom,(
% 0.20/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 0.20/0.59  fof(f328,plain,(
% 0.20/0.59    ~spl3_1 | ~spl3_2 | spl3_24 | ~spl3_3),
% 0.20/0.59    inference(avatar_split_clause,[],[f314,f112,f325,f107,f102])).
% 0.20/0.59  fof(f102,plain,(
% 0.20/0.59    spl3_1 <=> v2_pre_topc(sK0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.59  fof(f325,plain,(
% 0.20/0.59    spl3_24 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.59  fof(f314,plain,(
% 0.20/0.59    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_3),
% 0.20/0.59    inference(resolution,[],[f76,f114])).
% 0.20/0.59  fof(f76,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f43])).
% 0.20/0.59  fof(f43,plain,(
% 0.20/0.59    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.59    inference(flattening,[],[f42])).
% 0.20/0.59  fof(f42,plain,(
% 0.20/0.59    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f22])).
% 0.20/0.59  fof(f22,axiom,(
% 0.20/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.59  fof(f323,plain,(
% 0.20/0.59    ~spl3_23 | spl3_21),
% 0.20/0.59    inference(avatar_split_clause,[],[f318,f299,f320])).
% 0.20/0.59  fof(f318,plain,(
% 0.20/0.59    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl3_21),
% 0.20/0.59    inference(resolution,[],[f301,f89])).
% 0.20/0.59  fof(f89,plain,(
% 0.20/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f60])).
% 0.20/0.59  fof(f301,plain,(
% 0.20/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_21),
% 0.20/0.59    inference(avatar_component_clause,[],[f299])).
% 0.20/0.59  fof(f267,plain,(
% 0.20/0.59    spl3_14 | ~spl3_11),
% 0.20/0.59    inference(avatar_split_clause,[],[f255,f230,f264])).
% 0.20/0.59  fof(f255,plain,(
% 0.20/0.59    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_11),
% 0.20/0.59    inference(superposition,[],[f93,f232])).
% 0.20/0.59  fof(f243,plain,(
% 0.20/0.59    ~spl3_2 | ~spl3_3 | spl3_10),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f240])).
% 0.20/0.59  fof(f240,plain,(
% 0.20/0.59    $false | (~spl3_2 | ~spl3_3 | spl3_10)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f109,f114,f228,f72])).
% 0.20/0.59  fof(f72,plain,(
% 0.20/0.59    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f37])).
% 0.20/0.59  fof(f37,plain,(
% 0.20/0.59    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.59    inference(flattening,[],[f36])).
% 0.20/0.59  fof(f36,plain,(
% 0.20/0.59    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f20])).
% 0.20/0.59  fof(f20,axiom,(
% 0.20/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.20/0.59  fof(f228,plain,(
% 0.20/0.59    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_10),
% 0.20/0.59    inference(avatar_component_clause,[],[f226])).
% 0.20/0.59  fof(f226,plain,(
% 0.20/0.59    spl3_10 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.59  fof(f233,plain,(
% 0.20/0.59    ~spl3_10 | spl3_11 | ~spl3_5),
% 0.20/0.59    inference(avatar_split_clause,[],[f223,f121,f230,f226])).
% 0.20/0.59  fof(f223,plain,(
% 0.20/0.59    k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.20/0.59    inference(superposition,[],[f94,f123])).
% 0.20/0.59  fof(f123,plain,(
% 0.20/0.59    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_5),
% 0.20/0.59    inference(avatar_component_clause,[],[f121])).
% 0.20/0.59  fof(f127,plain,(
% 0.20/0.59    ~spl3_4 | ~spl3_5),
% 0.20/0.59    inference(avatar_split_clause,[],[f126,f121,f117])).
% 0.20/0.59  fof(f126,plain,(
% 0.20/0.59    ~v3_pre_topc(sK1,sK0) | ~spl3_5),
% 0.20/0.59    inference(trivial_inequality_removal,[],[f125])).
% 0.20/0.59  fof(f125,plain,(
% 0.20/0.59    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~spl3_5),
% 0.20/0.59    inference(forward_demodulation,[],[f67,f123])).
% 0.20/0.59  fof(f67,plain,(
% 0.20/0.59    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f56])).
% 0.20/0.59  fof(f56,plain,(
% 0.20/0.59    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f53,f55,f54])).
% 0.20/0.59  fof(f54,plain,(
% 0.20/0.59    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f55,plain,(
% 0.20/0.59    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f53,plain,(
% 0.20/0.59    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.59    inference(flattening,[],[f52])).
% 0.20/0.59  fof(f52,plain,(
% 0.20/0.59    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.59    inference(nnf_transformation,[],[f31])).
% 0.20/0.59  fof(f31,plain,(
% 0.20/0.59    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.59    inference(flattening,[],[f30])).
% 0.20/0.59  fof(f30,plain,(
% 0.20/0.59    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f29])).
% 0.20/0.59  fof(f29,negated_conjecture,(
% 0.20/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.20/0.59    inference(negated_conjecture,[],[f28])).
% 0.20/0.59  fof(f28,conjecture,(
% 0.20/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 0.20/0.59  fof(f124,plain,(
% 0.20/0.59    spl3_4 | spl3_5),
% 0.20/0.59    inference(avatar_split_clause,[],[f66,f121,f117])).
% 0.20/0.59  fof(f66,plain,(
% 0.20/0.59    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f56])).
% 0.20/0.59  fof(f115,plain,(
% 0.20/0.59    spl3_3),
% 0.20/0.59    inference(avatar_split_clause,[],[f65,f112])).
% 0.20/0.59  fof(f65,plain,(
% 0.20/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.59    inference(cnf_transformation,[],[f56])).
% 0.20/0.59  fof(f110,plain,(
% 0.20/0.59    spl3_2),
% 0.20/0.59    inference(avatar_split_clause,[],[f64,f107])).
% 0.20/0.59  fof(f64,plain,(
% 0.20/0.59    l1_pre_topc(sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f56])).
% 0.20/0.59  fof(f105,plain,(
% 0.20/0.59    spl3_1),
% 0.20/0.59    inference(avatar_split_clause,[],[f63,f102])).
% 0.20/0.59  fof(f63,plain,(
% 0.20/0.59    v2_pre_topc(sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f56])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (16984)------------------------------
% 0.20/0.59  % (16984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (16984)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (16984)Memory used [KB]: 11641
% 0.20/0.59  % (16984)Time elapsed: 0.163 s
% 0.20/0.59  % (16984)------------------------------
% 0.20/0.59  % (16984)------------------------------
% 0.20/0.59  % (16960)Success in time 0.237 s
%------------------------------------------------------------------------------
