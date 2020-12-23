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
% DateTime   : Thu Dec  3 13:12:22 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  242 ( 652 expanded)
%              Number of leaves         :   51 ( 237 expanded)
%              Depth                    :   12
%              Number of atoms          :  745 (1947 expanded)
%              Number of equality atoms :  101 ( 356 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2448,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f114,f126,f133,f149,f185,f250,f257,f331,f349,f373,f389,f459,f489,f591,f667,f753,f769,f788,f918,f1117,f1204,f1347,f1377,f1552,f1612,f1657,f2026,f2031,f2075,f2311,f2356,f2363,f2413,f2414,f2447])).

fof(f2447,plain,
    ( ~ spl3_3
    | spl3_5
    | ~ spl3_34
    | ~ spl3_58 ),
    inference(avatar_contradiction_clause,[],[f2446])).

fof(f2446,plain,
    ( $false
    | ~ spl3_3
    | spl3_5
    | ~ spl3_34
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f2445,f124])).

fof(f124,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_5
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f2445,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_34
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f476,f768])).

fof(f768,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f766])).

fof(f766,plain,
    ( spl3_58
  <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f476,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_3
    | ~ spl3_34 ),
    inference(resolution,[],[f458,f113])).

fof(f113,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f458,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl3_34
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f2414,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,u1_struct_0(sK0))
    | u1_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))
    | k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2413,plain,
    ( spl3_142
    | ~ spl3_60
    | ~ spl3_93
    | ~ spl3_130 ),
    inference(avatar_split_clause,[],[f2369,f2029,f1362,f785,f2308])).

fof(f2308,plain,
    ( spl3_142
  <=> u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_142])])).

fof(f785,plain,
    ( spl3_60
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f1362,plain,
    ( spl3_93
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f2029,plain,
    ( spl3_130
  <=> ! [X0] :
        ( u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
        | ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_130])])).

fof(f2369,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_60
    | ~ spl3_93
    | ~ spl3_130 ),
    inference(subsumption_resolution,[],[f2360,f1363])).

fof(f1363,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_93 ),
    inference(avatar_component_clause,[],[f1362])).

fof(f2360,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_60
    | ~ spl3_130 ),
    inference(resolution,[],[f787,f2030])).

fof(f2030,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_130 ),
    inference(avatar_component_clause,[],[f2029])).

fof(f787,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f785])).

fof(f2363,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | spl3_4
    | ~ spl3_60 ),
    inference(avatar_contradiction_clause,[],[f2358])).

fof(f2358,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | spl3_4
    | ~ spl3_60 ),
    inference(unit_resulting_resolution,[],[f103,f120,f113,f787,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f120,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_4
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f103,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f2356,plain,
    ( spl3_60
    | ~ spl3_1
    | ~ spl3_93
    | ~ spl3_129
    | ~ spl3_142 ),
    inference(avatar_split_clause,[],[f2355,f2308,f2023,f1362,f101,f785])).

fof(f2023,plain,
    ( spl3_129
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_129])])).

fof(f2355,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_1
    | ~ spl3_93
    | ~ spl3_129
    | ~ spl3_142 ),
    inference(subsumption_resolution,[],[f2354,f103])).

fof(f2354,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_93
    | ~ spl3_129
    | ~ spl3_142 ),
    inference(subsumption_resolution,[],[f2353,f1363])).

fof(f2353,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_129
    | ~ spl3_142 ),
    inference(subsumption_resolution,[],[f2352,f2025])).

fof(f2025,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_129 ),
    inference(avatar_component_clause,[],[f2023])).

fof(f2352,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_142 ),
    inference(superposition,[],[f78,f2310])).

fof(f2310,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_142 ),
    inference(avatar_component_clause,[],[f2308])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f2311,plain,
    ( spl3_142
    | ~ spl3_58
    | ~ spl3_135 ),
    inference(avatar_split_clause,[],[f2276,f2070,f766,f2308])).

fof(f2070,plain,
    ( spl3_135
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_135])])).

fof(f2276,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_58
    | ~ spl3_135 ),
    inference(forward_demodulation,[],[f2275,f1052])).

fof(f1052,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f319,f1046])).

fof(f1046,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(subsumption_resolution,[],[f1035,f98])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1035,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_subset_1(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f422,f258])).

fof(f258,plain,(
    ! [X0] : r1_tarski(k3_subset_1(X0,X0),X0) ),
    inference(resolution,[],[f205,f98])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r1_tarski(k3_subset_1(X0,X1),X0) ) ),
    inference(resolution,[],[f144,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(k3_subset_1(X1,X0),X1) ) ),
    inference(resolution,[],[f82,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f422,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | k1_xboole_0 = k3_subset_1(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f186,f94])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | k1_xboole_0 = k3_subset_1(X0,X1) ) ),
    inference(resolution,[],[f95,f98])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f319,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(resolution,[],[f157,f98])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f84,f94])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2275,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_58
    | ~ spl3_135 ),
    inference(forward_demodulation,[],[f2253,f768])).

fof(f2253,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl3_135 ),
    inference(resolution,[],[f2072,f84])).

fof(f2072,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_135 ),
    inference(avatar_component_clause,[],[f2070])).

fof(f2075,plain,
    ( spl3_135
    | ~ spl3_23
    | ~ spl3_93 ),
    inference(avatar_split_clause,[],[f1383,f1362,f347,f2070])).

fof(f347,plain,
    ( spl3_23
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f1383,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_23
    | ~ spl3_93 ),
    inference(resolution,[],[f1363,f348])).

fof(f348,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f347])).

fof(f2031,plain,
    ( spl3_130
    | ~ spl3_28
    | ~ spl3_90
    | ~ spl3_102
    | ~ spl3_103 ),
    inference(avatar_split_clause,[],[f2008,f1654,f1609,f1344,f387,f2029])).

fof(f387,plain,
    ( spl3_28
  <=> ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f1344,plain,
    ( spl3_90
  <=> m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).

fof(f1609,plain,
    ( spl3_102
  <=> v1_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_102])])).

fof(f1654,plain,
    ( spl3_103
  <=> u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).

fof(f2008,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = k2_pre_topc(sK0,X0)
        | ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_28
    | ~ spl3_90
    | ~ spl3_102
    | ~ spl3_103 ),
    inference(backward_demodulation,[],[f388,f2006])).

fof(f2006,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_28
    | ~ spl3_90
    | ~ spl3_102
    | ~ spl3_103 ),
    inference(forward_demodulation,[],[f2005,f1656])).

fof(f1656,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ spl3_103 ),
    inference(avatar_component_clause,[],[f1654])).

fof(f2005,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ spl3_28
    | ~ spl3_90
    | ~ spl3_102
    | ~ spl3_103 ),
    inference(forward_demodulation,[],[f1645,f1656])).

fof(f1645,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl3_28
    | ~ spl3_90
    | ~ spl3_102 ),
    inference(subsumption_resolution,[],[f1643,f1346])).

fof(f1346,plain,
    ( m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_90 ),
    inference(avatar_component_clause,[],[f1344])).

fof(f1643,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k2_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl3_28
    | ~ spl3_102 ),
    inference(resolution,[],[f1611,f388])).

fof(f1611,plain,
    ( v1_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0)
    | ~ spl3_102 ),
    inference(avatar_component_clause,[],[f1609])).

fof(f388,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f387])).

fof(f2026,plain,
    ( spl3_129
    | ~ spl3_28
    | ~ spl3_90
    | ~ spl3_102
    | ~ spl3_103 ),
    inference(avatar_split_clause,[],[f2006,f1654,f1609,f1344,f387,f2023])).

fof(f1657,plain,
    ( spl3_103
    | ~ spl3_76
    | ~ spl3_90 ),
    inference(avatar_split_clause,[],[f1541,f1344,f1114,f1654])).

fof(f1114,plain,
    ( spl3_76
  <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f1541,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ spl3_76
    | ~ spl3_90 ),
    inference(forward_demodulation,[],[f1540,f1052])).

fof(f1540,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ spl3_76
    | ~ spl3_90 ),
    inference(forward_demodulation,[],[f1525,f1116])).

fof(f1116,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl3_76 ),
    inference(avatar_component_clause,[],[f1114])).

fof(f1525,plain,
    ( k2_pre_topc(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))))
    | ~ spl3_90 ),
    inference(resolution,[],[f1346,f84])).

fof(f1612,plain,
    ( spl3_102
    | ~ spl3_50
    | ~ spl3_90
    | ~ spl3_99 ),
    inference(avatar_split_clause,[],[f1564,f1550,f1344,f664,f1609])).

fof(f664,plain,
    ( spl3_50
  <=> r1_tarski(sK2(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f1550,plain,
    ( spl3_99
  <=> ! [X0] :
        ( ~ r1_tarski(sK2(sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).

fof(f1564,plain,
    ( v1_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0)
    | ~ spl3_50
    | ~ spl3_90
    | ~ spl3_99 ),
    inference(subsumption_resolution,[],[f1560,f1346])).

fof(f1560,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0)
    | ~ spl3_50
    | ~ spl3_99 ),
    inference(resolution,[],[f1551,f666])).

fof(f666,plain,
    ( r1_tarski(sK2(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f664])).

fof(f1551,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X0,sK0) )
    | ~ spl3_99 ),
    inference(avatar_component_clause,[],[f1550])).

fof(f1552,plain,
    ( spl3_99
    | ~ spl3_1
    | ~ spl3_36
    | ~ spl3_68 ),
    inference(avatar_split_clause,[],[f1513,f907,f487,f101,f1550])).

fof(f487,plain,
    ( spl3_36
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f907,plain,
    ( spl3_68
  <=> m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f1513,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X0,sK0) )
    | ~ spl3_1
    | ~ spl3_36
    | ~ spl3_68 ),
    inference(subsumption_resolution,[],[f498,f908])).

fof(f908,plain,
    ( m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_68 ),
    inference(avatar_component_clause,[],[f907])).

fof(f498,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X0,sK0) )
    | ~ spl3_1
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f496,f103])).

fof(f496,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(sK0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_36 ),
    inference(resolution,[],[f488,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v1_tops_1(sK2(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_tops_1(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_tops_1(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_tops_1)).

fof(f488,plain,
    ( ! [X0,X1] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X1,sK0) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f487])).

fof(f1377,plain,
    ( ~ spl3_3
    | spl3_93 ),
    inference(avatar_contradiction_clause,[],[f1376])).

fof(f1376,plain,
    ( $false
    | ~ spl3_3
    | spl3_93 ),
    inference(subsumption_resolution,[],[f1372,f113])).

fof(f1372,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_93 ),
    inference(resolution,[],[f1364,f82])).

fof(f1364,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_93 ),
    inference(avatar_component_clause,[],[f1362])).

fof(f1347,plain,
    ( spl3_90
    | ~ spl3_81 ),
    inference(avatar_split_clause,[],[f1265,f1202,f1344])).

fof(f1202,plain,
    ( spl3_81
  <=> ! [X1] :
        ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).

fof(f1265,plain,
    ( m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_81 ),
    inference(forward_demodulation,[],[f1253,f1052])).

fof(f1253,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_81 ),
    inference(resolution,[],[f1203,f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1203,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_81 ),
    inference(avatar_component_clause,[],[f1202])).

fof(f1204,plain,
    ( spl3_81
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f369,f347,f1202])).

fof(f369,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_23 ),
    inference(resolution,[],[f348,f82])).

fof(f1117,plain,
    ( spl3_76
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f1072,f750,f1114])).

fof(f750,plain,
    ( spl3_57
  <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f1072,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl3_57 ),
    inference(backward_demodulation,[],[f752,f1052])).

fof(f752,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f750])).

fof(f918,plain,
    ( ~ spl3_1
    | spl3_68 ),
    inference(avatar_contradiction_clause,[],[f917])).

fof(f917,plain,
    ( $false
    | ~ spl3_1
    | spl3_68 ),
    inference(subsumption_resolution,[],[f913,f103])).

fof(f913,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_68 ),
    inference(resolution,[],[f909,f80])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f909,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_68 ),
    inference(avatar_component_clause,[],[f907])).

fof(f788,plain,
    ( spl3_60
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f772,f119,f111,f101,f785])).

fof(f772,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f771,f103])).

fof(f771,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f770,f113])).

fof(f770,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f121,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f121,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f769,plain,
    ( spl3_58
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f479,f457,f123,f111,f766])).

fof(f479,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f476,f125])).

fof(f125,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f753,plain,
    ( spl3_57
    | ~ spl3_24
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f478,f457,f352,f750])).

fof(f352,plain,
    ( spl3_24
  <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f478,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_24
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f473,f354])).

fof(f354,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f352])).

fof(f473,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_34 ),
    inference(resolution,[],[f458,f70])).

fof(f667,plain,
    ( spl3_50
    | ~ spl3_11
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f636,f589,f183,f664])).

fof(f183,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK0),X0)
        | r1_tarski(sK2(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f589,plain,
    ( spl3_42
  <=> ! [X0] :
        ( r1_tarski(X0,k2_pre_topc(sK0,X0))
        | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f636,plain,
    ( r1_tarski(sK2(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl3_11
    | ~ spl3_42 ),
    inference(subsumption_resolution,[],[f634,f98])).

fof(f634,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | r1_tarski(sK2(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl3_11
    | ~ spl3_42 ),
    inference(resolution,[],[f590,f184])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK0),X0)
        | r1_tarski(sK2(sK0),X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f183])).

fof(f590,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_pre_topc(sK0,X0))
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f589])).

fof(f591,plain,
    ( spl3_42
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f277,f248,f589])).

fof(f248,plain,
    ( spl3_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f277,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_pre_topc(sK0,X0))
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl3_16 ),
    inference(resolution,[],[f249,f94])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f248])).

fof(f489,plain,
    ( spl3_36
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f241,f101,f487])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X1,sK0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f79,f103])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).

fof(f459,plain,
    ( spl3_34
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f233,f101,f457])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f73,f103])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f389,plain,
    ( spl3_28
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f201,f101,f387])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f77,f103])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f373,plain,
    ( spl3_24
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f345,f328,f352])).

fof(f328,plain,
    ( spl3_21
  <=> r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f345,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f342,f115])).

fof(f115,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f93,f70])).

fof(f342,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tops_1(sK0,k1_xboole_0))
    | k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl3_21 ),
    inference(resolution,[],[f330,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f330,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f328])).

fof(f349,plain,
    ( spl3_23
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f181,f101,f347])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f88,f103])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f331,plain,
    ( spl3_21
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f289,f255,f328])).

fof(f255,plain,
    ( spl3_17
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f289,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl3_17 ),
    inference(resolution,[],[f256,f70])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f255])).

fof(f257,plain,
    ( spl3_17
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f168,f101,f255])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f72,f103])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f250,plain,
    ( spl3_16
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f163,f101,f248])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k2_pre_topc(sK0,X0)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f71,f103])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f185,plain,
    ( spl3_11
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f150,f146,f183])).

fof(f146,plain,
    ( spl3_7
  <=> r1_tarski(sK2(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK0),X0)
        | r1_tarski(sK2(sK0),X0) )
    | ~ spl3_7 ),
    inference(resolution,[],[f148,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f148,plain,
    ( r1_tarski(sK2(sK0),u1_struct_0(sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f146])).

fof(f149,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f143,f101,f146])).

fof(f143,plain,
    ( r1_tarski(sK2(sK0),u1_struct_0(sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f134,f103])).

fof(f134,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(sK2(X0),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f80,f93])).

fof(f133,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f132,f123,f119])).

fof(f132,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f68,f125])).

fof(f68,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f53,f55,f54])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_xboole_0 != k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
            | ~ v2_tops_1(X1,sK0) )
          & ( k1_xboole_0 = k1_tops_1(sK0,X1)
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X1] :
        ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
          | ~ v2_tops_1(X1,sK0) )
        & ( k1_xboole_0 = k1_tops_1(sK0,X1)
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
        | ~ v2_tops_1(sK1,sK0) )
      & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f126,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f67,f123,f119])).

fof(f67,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f114,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f66,f111])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f104,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f65,f101])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (2251)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.49  % (2269)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.49  % (2254)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.49  % (2249)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.49  % (2248)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.50  % (2261)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.50  % (2268)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.50  % (2252)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.50  % (2256)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.51  % (2267)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.51  % (2259)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (2272)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.51  % (2260)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.51  % (2246)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.51  % (2265)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.51  % (2247)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (2264)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.27/0.52  % (2250)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.27/0.52  % (2257)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.27/0.52  % (2271)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.27/0.53  % (2262)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.43/0.53  % (2258)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.43/0.54  % (2255)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.43/0.54  % (2253)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.43/0.54  % (2266)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.43/0.55  % (2263)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 2.14/0.64  % (2248)Refutation found. Thanks to Tanya!
% 2.14/0.64  % SZS status Theorem for theBenchmark
% 2.14/0.64  % SZS output start Proof for theBenchmark
% 2.14/0.65  fof(f2448,plain,(
% 2.14/0.65    $false),
% 2.14/0.65    inference(avatar_sat_refutation,[],[f104,f114,f126,f133,f149,f185,f250,f257,f331,f349,f373,f389,f459,f489,f591,f667,f753,f769,f788,f918,f1117,f1204,f1347,f1377,f1552,f1612,f1657,f2026,f2031,f2075,f2311,f2356,f2363,f2413,f2414,f2447])).
% 2.14/0.65  fof(f2447,plain,(
% 2.14/0.65    ~spl3_3 | spl3_5 | ~spl3_34 | ~spl3_58),
% 2.14/0.65    inference(avatar_contradiction_clause,[],[f2446])).
% 2.14/0.65  fof(f2446,plain,(
% 2.14/0.65    $false | (~spl3_3 | spl3_5 | ~spl3_34 | ~spl3_58)),
% 2.14/0.65    inference(subsumption_resolution,[],[f2445,f124])).
% 2.14/0.65  fof(f124,plain,(
% 2.14/0.65    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl3_5),
% 2.14/0.65    inference(avatar_component_clause,[],[f123])).
% 2.14/0.65  fof(f123,plain,(
% 2.14/0.65    spl3_5 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.14/0.65  fof(f2445,plain,(
% 2.14/0.65    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl3_3 | ~spl3_34 | ~spl3_58)),
% 2.14/0.65    inference(forward_demodulation,[],[f476,f768])).
% 2.14/0.65  fof(f768,plain,(
% 2.14/0.65    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl3_58),
% 2.14/0.65    inference(avatar_component_clause,[],[f766])).
% 2.14/0.65  fof(f766,plain,(
% 2.14/0.65    spl3_58 <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 2.14/0.65  fof(f476,plain,(
% 2.14/0.65    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl3_3 | ~spl3_34)),
% 2.14/0.65    inference(resolution,[],[f458,f113])).
% 2.14/0.65  fof(f113,plain,(
% 2.14/0.65    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.14/0.65    inference(avatar_component_clause,[],[f111])).
% 2.14/0.65  fof(f111,plain,(
% 2.14/0.65    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.14/0.65  fof(f458,plain,(
% 2.14/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | ~spl3_34),
% 2.14/0.65    inference(avatar_component_clause,[],[f457])).
% 2.14/0.65  fof(f457,plain,(
% 2.14/0.65    spl3_34 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 2.14/0.65  fof(f2414,plain,(
% 2.14/0.65    u1_struct_0(sK0) != k2_pre_topc(sK0,u1_struct_0(sK0)) | u1_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | u1_struct_0(sK0) != k2_struct_0(sK0) | k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) | k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 2.14/0.65    introduced(theory_tautology_sat_conflict,[])).
% 2.14/0.65  fof(f2413,plain,(
% 2.14/0.65    spl3_142 | ~spl3_60 | ~spl3_93 | ~spl3_130),
% 2.14/0.65    inference(avatar_split_clause,[],[f2369,f2029,f1362,f785,f2308])).
% 2.14/0.65  fof(f2308,plain,(
% 2.14/0.65    spl3_142 <=> u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_142])])).
% 2.14/0.65  fof(f785,plain,(
% 2.14/0.65    spl3_60 <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 2.14/0.65  fof(f1362,plain,(
% 2.14/0.65    spl3_93 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 2.14/0.65  fof(f2029,plain,(
% 2.14/0.65    spl3_130 <=> ! [X0] : (u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_130])])).
% 2.14/0.65  fof(f2369,plain,(
% 2.14/0.65    u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_60 | ~spl3_93 | ~spl3_130)),
% 2.14/0.65    inference(subsumption_resolution,[],[f2360,f1363])).
% 2.14/0.65  fof(f1363,plain,(
% 2.14/0.65    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_93),
% 2.14/0.65    inference(avatar_component_clause,[],[f1362])).
% 2.14/0.65  fof(f2360,plain,(
% 2.14/0.65    u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_60 | ~spl3_130)),
% 2.14/0.65    inference(resolution,[],[f787,f2030])).
% 2.14/0.65  fof(f2030,plain,(
% 2.14/0.65    ( ! [X0] : (~v1_tops_1(X0,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_130),
% 2.14/0.65    inference(avatar_component_clause,[],[f2029])).
% 2.14/0.65  fof(f787,plain,(
% 2.14/0.65    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl3_60),
% 2.14/0.65    inference(avatar_component_clause,[],[f785])).
% 2.14/0.65  fof(f2363,plain,(
% 2.14/0.65    ~spl3_1 | ~spl3_3 | spl3_4 | ~spl3_60),
% 2.14/0.65    inference(avatar_contradiction_clause,[],[f2358])).
% 2.14/0.65  fof(f2358,plain,(
% 2.14/0.65    $false | (~spl3_1 | ~spl3_3 | spl3_4 | ~spl3_60)),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f103,f120,f113,f787,f76])).
% 2.14/0.65  fof(f76,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f57])).
% 2.14/0.65  fof(f57,plain,(
% 2.14/0.65    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.65    inference(nnf_transformation,[],[f31])).
% 2.14/0.65  fof(f31,plain,(
% 2.14/0.65    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.65    inference(ennf_transformation,[],[f18])).
% 2.14/0.65  fof(f18,axiom,(
% 2.14/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).
% 2.14/0.65  fof(f120,plain,(
% 2.14/0.65    ~v2_tops_1(sK1,sK0) | spl3_4),
% 2.14/0.65    inference(avatar_component_clause,[],[f119])).
% 2.14/0.65  fof(f119,plain,(
% 2.14/0.65    spl3_4 <=> v2_tops_1(sK1,sK0)),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.14/0.65  fof(f103,plain,(
% 2.14/0.65    l1_pre_topc(sK0) | ~spl3_1),
% 2.14/0.65    inference(avatar_component_clause,[],[f101])).
% 2.14/0.65  fof(f101,plain,(
% 2.14/0.65    spl3_1 <=> l1_pre_topc(sK0)),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.14/0.65  fof(f2356,plain,(
% 2.14/0.65    spl3_60 | ~spl3_1 | ~spl3_93 | ~spl3_129 | ~spl3_142),
% 2.14/0.65    inference(avatar_split_clause,[],[f2355,f2308,f2023,f1362,f101,f785])).
% 2.14/0.65  fof(f2023,plain,(
% 2.14/0.65    spl3_129 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_129])])).
% 2.14/0.65  fof(f2355,plain,(
% 2.14/0.65    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl3_1 | ~spl3_93 | ~spl3_129 | ~spl3_142)),
% 2.14/0.65    inference(subsumption_resolution,[],[f2354,f103])).
% 2.14/0.65  fof(f2354,plain,(
% 2.14/0.65    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | (~spl3_93 | ~spl3_129 | ~spl3_142)),
% 2.14/0.65    inference(subsumption_resolution,[],[f2353,f1363])).
% 2.14/0.65  fof(f2353,plain,(
% 2.14/0.65    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_129 | ~spl3_142)),
% 2.14/0.65    inference(subsumption_resolution,[],[f2352,f2025])).
% 2.14/0.65  fof(f2025,plain,(
% 2.14/0.65    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_129),
% 2.14/0.65    inference(avatar_component_clause,[],[f2023])).
% 2.14/0.65  fof(f2352,plain,(
% 2.14/0.65    u1_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_142),
% 2.14/0.65    inference(superposition,[],[f78,f2310])).
% 2.14/0.65  fof(f2310,plain,(
% 2.14/0.65    u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_142),
% 2.14/0.65    inference(avatar_component_clause,[],[f2308])).
% 2.14/0.65  fof(f78,plain,(
% 2.14/0.65    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != k2_struct_0(X0) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f58])).
% 2.14/0.65  fof(f58,plain,(
% 2.14/0.65    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.65    inference(nnf_transformation,[],[f32])).
% 2.14/0.65  fof(f32,plain,(
% 2.14/0.65    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.65    inference(ennf_transformation,[],[f17])).
% 2.14/0.65  fof(f17,axiom,(
% 2.14/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 2.14/0.65  fof(f2311,plain,(
% 2.14/0.65    spl3_142 | ~spl3_58 | ~spl3_135),
% 2.14/0.65    inference(avatar_split_clause,[],[f2276,f2070,f766,f2308])).
% 2.14/0.65  fof(f2070,plain,(
% 2.14/0.65    spl3_135 <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_135])])).
% 2.14/0.65  fof(f2276,plain,(
% 2.14/0.65    u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_58 | ~spl3_135)),
% 2.14/0.65    inference(forward_demodulation,[],[f2275,f1052])).
% 2.14/0.65  fof(f1052,plain,(
% 2.14/0.65    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 2.14/0.65    inference(backward_demodulation,[],[f319,f1046])).
% 2.14/0.65  fof(f1046,plain,(
% 2.14/0.65    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 2.14/0.65    inference(subsumption_resolution,[],[f1035,f98])).
% 2.14/0.65  fof(f98,plain,(
% 2.14/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.14/0.65    inference(equality_resolution,[],[f91])).
% 2.14/0.65  fof(f91,plain,(
% 2.14/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.14/0.65    inference(cnf_transformation,[],[f63])).
% 2.14/0.65  fof(f63,plain,(
% 2.14/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.65    inference(flattening,[],[f62])).
% 2.14/0.65  fof(f62,plain,(
% 2.14/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.65    inference(nnf_transformation,[],[f2])).
% 2.14/0.65  fof(f2,axiom,(
% 2.14/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.14/0.65  fof(f1035,plain,(
% 2.14/0.65    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0) | ~r1_tarski(X0,X0)) )),
% 2.14/0.65    inference(resolution,[],[f422,f258])).
% 2.14/0.65  fof(f258,plain,(
% 2.14/0.65    ( ! [X0] : (r1_tarski(k3_subset_1(X0,X0),X0)) )),
% 2.14/0.65    inference(resolution,[],[f205,f98])).
% 2.14/0.65  fof(f205,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | r1_tarski(k3_subset_1(X0,X1),X0)) )),
% 2.14/0.65    inference(resolution,[],[f144,f94])).
% 2.14/0.65  fof(f94,plain,(
% 2.14/0.65    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f64])).
% 2.14/0.65  fof(f64,plain,(
% 2.14/0.65    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.14/0.65    inference(nnf_transformation,[],[f10])).
% 2.14/0.65  fof(f10,axiom,(
% 2.14/0.65    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.14/0.65  fof(f144,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(k3_subset_1(X1,X0),X1)) )),
% 2.14/0.65    inference(resolution,[],[f82,f93])).
% 2.14/0.65  fof(f93,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f64])).
% 2.14/0.65  fof(f82,plain,(
% 2.14/0.65    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f36])).
% 2.14/0.65  fof(f36,plain,(
% 2.14/0.65    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.14/0.65    inference(ennf_transformation,[],[f5])).
% 2.14/0.65  fof(f5,axiom,(
% 2.14/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.14/0.65  fof(f422,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r1_tarski(k3_subset_1(X0,X1),X1) | k1_xboole_0 = k3_subset_1(X0,X1) | ~r1_tarski(X1,X0)) )),
% 2.14/0.65    inference(resolution,[],[f186,f94])).
% 2.14/0.65  fof(f186,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(k3_subset_1(X0,X1),X1) | k1_xboole_0 = k3_subset_1(X0,X1)) )),
% 2.14/0.65    inference(resolution,[],[f95,f98])).
% 2.14/0.65  fof(f95,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f47])).
% 2.14/0.65  fof(f47,plain,(
% 2.14/0.65    ! [X0,X1,X2] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.14/0.65    inference(flattening,[],[f46])).
% 2.14/0.65  fof(f46,plain,(
% 2.14/0.65    ! [X0,X1,X2] : ((k1_xboole_0 = X1 | (~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.14/0.65    inference(ennf_transformation,[],[f8])).
% 2.14/0.65  fof(f8,axiom,(
% 2.14/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 2.14/0.65  fof(f319,plain,(
% 2.14/0.65    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,X0)) = X0) )),
% 2.14/0.65    inference(resolution,[],[f157,f98])).
% 2.14/0.65  fof(f157,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.14/0.65    inference(resolution,[],[f84,f94])).
% 2.14/0.65  fof(f84,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.14/0.65    inference(cnf_transformation,[],[f38])).
% 2.14/0.65  fof(f38,plain,(
% 2.14/0.65    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.14/0.65    inference(ennf_transformation,[],[f6])).
% 2.14/0.65  fof(f6,axiom,(
% 2.14/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.14/0.65  fof(f2275,plain,(
% 2.14/0.65    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl3_58 | ~spl3_135)),
% 2.14/0.65    inference(forward_demodulation,[],[f2253,f768])).
% 2.14/0.65  fof(f2253,plain,(
% 2.14/0.65    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl3_135),
% 2.14/0.65    inference(resolution,[],[f2072,f84])).
% 2.14/0.65  fof(f2072,plain,(
% 2.14/0.65    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_135),
% 2.14/0.65    inference(avatar_component_clause,[],[f2070])).
% 2.14/0.65  fof(f2075,plain,(
% 2.14/0.65    spl3_135 | ~spl3_23 | ~spl3_93),
% 2.14/0.65    inference(avatar_split_clause,[],[f1383,f1362,f347,f2070])).
% 2.14/0.65  fof(f347,plain,(
% 2.14/0.65    spl3_23 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.14/0.65  fof(f1383,plain,(
% 2.14/0.65    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_23 | ~spl3_93)),
% 2.14/0.65    inference(resolution,[],[f1363,f348])).
% 2.14/0.65  fof(f348,plain,(
% 2.14/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_23),
% 2.14/0.65    inference(avatar_component_clause,[],[f347])).
% 2.14/0.65  fof(f2031,plain,(
% 2.14/0.65    spl3_130 | ~spl3_28 | ~spl3_90 | ~spl3_102 | ~spl3_103),
% 2.14/0.65    inference(avatar_split_clause,[],[f2008,f1654,f1609,f1344,f387,f2029])).
% 2.14/0.65  fof(f387,plain,(
% 2.14/0.65    spl3_28 <=> ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_struct_0(sK0))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 2.14/0.65  fof(f1344,plain,(
% 2.14/0.65    spl3_90 <=> m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).
% 2.14/0.65  fof(f1609,plain,(
% 2.14/0.65    spl3_102 <=> v1_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0)),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_102])])).
% 2.14/0.65  fof(f1654,plain,(
% 2.14/0.65    spl3_103 <=> u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).
% 2.14/0.65  fof(f2008,plain,(
% 2.14/0.65    ( ! [X0] : (u1_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_28 | ~spl3_90 | ~spl3_102 | ~spl3_103)),
% 2.14/0.65    inference(backward_demodulation,[],[f388,f2006])).
% 2.14/0.65  fof(f2006,plain,(
% 2.14/0.65    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl3_28 | ~spl3_90 | ~spl3_102 | ~spl3_103)),
% 2.14/0.65    inference(forward_demodulation,[],[f2005,f1656])).
% 2.14/0.65  fof(f1656,plain,(
% 2.14/0.65    u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | ~spl3_103),
% 2.14/0.65    inference(avatar_component_clause,[],[f1654])).
% 2.14/0.65  fof(f2005,plain,(
% 2.14/0.65    k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | (~spl3_28 | ~spl3_90 | ~spl3_102 | ~spl3_103)),
% 2.14/0.65    inference(forward_demodulation,[],[f1645,f1656])).
% 2.14/0.65  fof(f1645,plain,(
% 2.14/0.65    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))) | (~spl3_28 | ~spl3_90 | ~spl3_102)),
% 2.14/0.65    inference(subsumption_resolution,[],[f1643,f1346])).
% 2.14/0.65  fof(f1346,plain,(
% 2.14/0.65    m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_90),
% 2.14/0.65    inference(avatar_component_clause,[],[f1344])).
% 2.14/0.65  fof(f1643,plain,(
% 2.14/0.65    ~m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))) | (~spl3_28 | ~spl3_102)),
% 2.14/0.65    inference(resolution,[],[f1611,f388])).
% 2.14/0.65  fof(f1611,plain,(
% 2.14/0.65    v1_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0) | ~spl3_102),
% 2.14/0.65    inference(avatar_component_clause,[],[f1609])).
% 2.14/0.65  fof(f388,plain,(
% 2.14/0.65    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)) ) | ~spl3_28),
% 2.14/0.65    inference(avatar_component_clause,[],[f387])).
% 2.14/0.65  fof(f2026,plain,(
% 2.14/0.65    spl3_129 | ~spl3_28 | ~spl3_90 | ~spl3_102 | ~spl3_103),
% 2.14/0.65    inference(avatar_split_clause,[],[f2006,f1654,f1609,f1344,f387,f2023])).
% 2.14/0.65  fof(f1657,plain,(
% 2.14/0.65    spl3_103 | ~spl3_76 | ~spl3_90),
% 2.14/0.65    inference(avatar_split_clause,[],[f1541,f1344,f1114,f1654])).
% 2.14/0.65  fof(f1114,plain,(
% 2.14/0.65    spl3_76 <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 2.14/0.65  fof(f1541,plain,(
% 2.14/0.65    u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | (~spl3_76 | ~spl3_90)),
% 2.14/0.65    inference(forward_demodulation,[],[f1540,f1052])).
% 2.14/0.65  fof(f1540,plain,(
% 2.14/0.65    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | (~spl3_76 | ~spl3_90)),
% 2.14/0.65    inference(forward_demodulation,[],[f1525,f1116])).
% 2.14/0.65  fof(f1116,plain,(
% 2.14/0.65    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) | ~spl3_76),
% 2.14/0.65    inference(avatar_component_clause,[],[f1114])).
% 2.14/0.65  fof(f1525,plain,(
% 2.14/0.65    k2_pre_topc(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))) | ~spl3_90),
% 2.14/0.65    inference(resolution,[],[f1346,f84])).
% 2.14/0.65  fof(f1612,plain,(
% 2.14/0.65    spl3_102 | ~spl3_50 | ~spl3_90 | ~spl3_99),
% 2.14/0.65    inference(avatar_split_clause,[],[f1564,f1550,f1344,f664,f1609])).
% 2.14/0.65  fof(f664,plain,(
% 2.14/0.65    spl3_50 <=> r1_tarski(sK2(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 2.14/0.65  fof(f1550,plain,(
% 2.14/0.65    spl3_99 <=> ! [X0] : (~r1_tarski(sK2(sK0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).
% 2.14/0.65  fof(f1564,plain,(
% 2.14/0.65    v1_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0) | (~spl3_50 | ~spl3_90 | ~spl3_99)),
% 2.14/0.65    inference(subsumption_resolution,[],[f1560,f1346])).
% 2.14/0.65  fof(f1560,plain,(
% 2.14/0.65    ~m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0) | (~spl3_50 | ~spl3_99)),
% 2.14/0.65    inference(resolution,[],[f1551,f666])).
% 2.14/0.65  fof(f666,plain,(
% 2.14/0.65    r1_tarski(sK2(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) | ~spl3_50),
% 2.14/0.65    inference(avatar_component_clause,[],[f664])).
% 2.14/0.65  fof(f1551,plain,(
% 2.14/0.65    ( ! [X0] : (~r1_tarski(sK2(sK0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0)) ) | ~spl3_99),
% 2.14/0.65    inference(avatar_component_clause,[],[f1550])).
% 2.14/0.65  fof(f1552,plain,(
% 2.14/0.65    spl3_99 | ~spl3_1 | ~spl3_36 | ~spl3_68),
% 2.14/0.65    inference(avatar_split_clause,[],[f1513,f907,f487,f101,f1550])).
% 2.14/0.65  fof(f487,plain,(
% 2.14/0.65    spl3_36 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | ~v1_tops_1(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X1,sK0))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 2.14/0.65  fof(f907,plain,(
% 2.14/0.65    spl3_68 <=> m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 2.14/0.65  fof(f1513,plain,(
% 2.14/0.65    ( ! [X0] : (~r1_tarski(sK2(sK0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0)) ) | (~spl3_1 | ~spl3_36 | ~spl3_68)),
% 2.14/0.65    inference(subsumption_resolution,[],[f498,f908])).
% 2.14/0.65  fof(f908,plain,(
% 2.14/0.65    m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_68),
% 2.14/0.65    inference(avatar_component_clause,[],[f907])).
% 2.14/0.65  fof(f498,plain,(
% 2.14/0.65    ( ! [X0] : (~r1_tarski(sK2(sK0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0)) ) | (~spl3_1 | ~spl3_36)),
% 2.14/0.65    inference(subsumption_resolution,[],[f496,f103])).
% 2.14/0.65  fof(f496,plain,(
% 2.14/0.65    ( ! [X0] : (~r1_tarski(sK2(sK0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0) | ~l1_pre_topc(sK0)) ) | ~spl3_36),
% 2.14/0.65    inference(resolution,[],[f488,f81])).
% 2.14/0.65  fof(f81,plain,(
% 2.14/0.65    ( ! [X0] : (v1_tops_1(sK2(X0),X0) | ~l1_pre_topc(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f60])).
% 2.14/0.65  fof(f60,plain,(
% 2.14/0.65    ! [X0] : ((v1_tops_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f59])).
% 2.14/0.65  fof(f59,plain,(
% 2.14/0.65    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.14/0.65    introduced(choice_axiom,[])).
% 2.14/0.65  fof(f35,plain,(
% 2.14/0.65    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.65    inference(ennf_transformation,[],[f20])).
% 2.14/0.65  fof(f20,axiom,(
% 2.14/0.65    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_tops_1)).
% 2.14/0.65  fof(f488,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~v1_tops_1(X0,sK0) | ~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X1,sK0)) ) | ~spl3_36),
% 2.14/0.65    inference(avatar_component_clause,[],[f487])).
% 2.14/0.65  fof(f1377,plain,(
% 2.14/0.65    ~spl3_3 | spl3_93),
% 2.14/0.65    inference(avatar_contradiction_clause,[],[f1376])).
% 2.14/0.65  fof(f1376,plain,(
% 2.14/0.65    $false | (~spl3_3 | spl3_93)),
% 2.14/0.65    inference(subsumption_resolution,[],[f1372,f113])).
% 2.14/0.65  fof(f1372,plain,(
% 2.14/0.65    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_93),
% 2.14/0.65    inference(resolution,[],[f1364,f82])).
% 2.14/0.65  fof(f1364,plain,(
% 2.14/0.65    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_93),
% 2.14/0.65    inference(avatar_component_clause,[],[f1362])).
% 2.14/0.65  fof(f1347,plain,(
% 2.14/0.65    spl3_90 | ~spl3_81),
% 2.14/0.65    inference(avatar_split_clause,[],[f1265,f1202,f1344])).
% 2.14/0.65  fof(f1202,plain,(
% 2.14/0.65    spl3_81 <=> ! [X1] : (m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).
% 2.14/0.65  fof(f1265,plain,(
% 2.14/0.65    m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_81),
% 2.14/0.65    inference(forward_demodulation,[],[f1253,f1052])).
% 2.14/0.65  fof(f1253,plain,(
% 2.14/0.65    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_81),
% 2.14/0.65    inference(resolution,[],[f1203,f70])).
% 2.14/0.65  fof(f70,plain,(
% 2.14/0.65    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f9])).
% 2.14/0.65  fof(f9,axiom,(
% 2.14/0.65    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.14/0.65  fof(f1203,plain,(
% 2.14/0.65    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_81),
% 2.14/0.65    inference(avatar_component_clause,[],[f1202])).
% 2.14/0.65  fof(f1204,plain,(
% 2.14/0.65    spl3_81 | ~spl3_23),
% 2.14/0.65    inference(avatar_split_clause,[],[f369,f347,f1202])).
% 2.14/0.65  fof(f369,plain,(
% 2.14/0.65    ( ! [X1] : (m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_23),
% 2.14/0.65    inference(resolution,[],[f348,f82])).
% 2.14/0.65  fof(f1117,plain,(
% 2.14/0.65    spl3_76 | ~spl3_57),
% 2.14/0.65    inference(avatar_split_clause,[],[f1072,f750,f1114])).
% 2.14/0.65  fof(f750,plain,(
% 2.14/0.65    spl3_57 <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 2.14/0.65  fof(f1072,plain,(
% 2.14/0.65    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) | ~spl3_57),
% 2.14/0.65    inference(backward_demodulation,[],[f752,f1052])).
% 2.14/0.65  fof(f752,plain,(
% 2.14/0.65    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))) | ~spl3_57),
% 2.14/0.65    inference(avatar_component_clause,[],[f750])).
% 2.14/0.65  fof(f918,plain,(
% 2.14/0.65    ~spl3_1 | spl3_68),
% 2.14/0.65    inference(avatar_contradiction_clause,[],[f917])).
% 2.14/0.65  fof(f917,plain,(
% 2.14/0.65    $false | (~spl3_1 | spl3_68)),
% 2.14/0.65    inference(subsumption_resolution,[],[f913,f103])).
% 2.14/0.65  fof(f913,plain,(
% 2.14/0.65    ~l1_pre_topc(sK0) | spl3_68),
% 2.14/0.65    inference(resolution,[],[f909,f80])).
% 2.14/0.65  fof(f80,plain,(
% 2.14/0.65    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f60])).
% 2.14/0.65  fof(f909,plain,(
% 2.14/0.65    ~m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_68),
% 2.14/0.65    inference(avatar_component_clause,[],[f907])).
% 2.14/0.65  fof(f788,plain,(
% 2.14/0.65    spl3_60 | ~spl3_1 | ~spl3_3 | ~spl3_4),
% 2.14/0.65    inference(avatar_split_clause,[],[f772,f119,f111,f101,f785])).
% 2.14/0.65  fof(f772,plain,(
% 2.14/0.65    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl3_1 | ~spl3_3 | ~spl3_4)),
% 2.14/0.65    inference(subsumption_resolution,[],[f771,f103])).
% 2.14/0.65  fof(f771,plain,(
% 2.14/0.65    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | (~spl3_3 | ~spl3_4)),
% 2.14/0.65    inference(subsumption_resolution,[],[f770,f113])).
% 2.14/0.65  fof(f770,plain,(
% 2.14/0.65    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_4),
% 2.14/0.65    inference(resolution,[],[f121,f75])).
% 2.14/0.65  fof(f75,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f57])).
% 2.14/0.65  fof(f121,plain,(
% 2.14/0.65    v2_tops_1(sK1,sK0) | ~spl3_4),
% 2.14/0.65    inference(avatar_component_clause,[],[f119])).
% 2.14/0.65  fof(f769,plain,(
% 2.14/0.65    spl3_58 | ~spl3_3 | ~spl3_5 | ~spl3_34),
% 2.14/0.65    inference(avatar_split_clause,[],[f479,f457,f123,f111,f766])).
% 2.14/0.65  fof(f479,plain,(
% 2.14/0.65    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl3_3 | ~spl3_5 | ~spl3_34)),
% 2.14/0.65    inference(forward_demodulation,[],[f476,f125])).
% 2.14/0.65  fof(f125,plain,(
% 2.14/0.65    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl3_5),
% 2.14/0.65    inference(avatar_component_clause,[],[f123])).
% 2.14/0.65  fof(f753,plain,(
% 2.14/0.65    spl3_57 | ~spl3_24 | ~spl3_34),
% 2.14/0.65    inference(avatar_split_clause,[],[f478,f457,f352,f750])).
% 2.14/0.65  fof(f352,plain,(
% 2.14/0.65    spl3_24 <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.14/0.65  fof(f478,plain,(
% 2.14/0.65    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))) | (~spl3_24 | ~spl3_34)),
% 2.14/0.65    inference(forward_demodulation,[],[f473,f354])).
% 2.14/0.65  fof(f354,plain,(
% 2.14/0.65    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | ~spl3_24),
% 2.14/0.65    inference(avatar_component_clause,[],[f352])).
% 2.14/0.65  fof(f473,plain,(
% 2.14/0.65    k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))) | ~spl3_34),
% 2.14/0.65    inference(resolution,[],[f458,f70])).
% 2.14/0.65  fof(f667,plain,(
% 2.14/0.65    spl3_50 | ~spl3_11 | ~spl3_42),
% 2.14/0.65    inference(avatar_split_clause,[],[f636,f589,f183,f664])).
% 2.14/0.65  fof(f183,plain,(
% 2.14/0.65    spl3_11 <=> ! [X0] : (~r1_tarski(u1_struct_0(sK0),X0) | r1_tarski(sK2(sK0),X0))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.14/0.65  fof(f589,plain,(
% 2.14/0.65    spl3_42 <=> ! [X0] : (r1_tarski(X0,k2_pre_topc(sK0,X0)) | ~r1_tarski(X0,u1_struct_0(sK0)))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 2.14/0.65  fof(f636,plain,(
% 2.14/0.65    r1_tarski(sK2(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) | (~spl3_11 | ~spl3_42)),
% 2.14/0.65    inference(subsumption_resolution,[],[f634,f98])).
% 2.14/0.65  fof(f634,plain,(
% 2.14/0.65    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | r1_tarski(sK2(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) | (~spl3_11 | ~spl3_42)),
% 2.14/0.65    inference(resolution,[],[f590,f184])).
% 2.14/0.65  fof(f184,plain,(
% 2.14/0.65    ( ! [X0] : (~r1_tarski(u1_struct_0(sK0),X0) | r1_tarski(sK2(sK0),X0)) ) | ~spl3_11),
% 2.14/0.65    inference(avatar_component_clause,[],[f183])).
% 2.14/0.65  fof(f590,plain,(
% 2.14/0.65    ( ! [X0] : (r1_tarski(X0,k2_pre_topc(sK0,X0)) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl3_42),
% 2.14/0.65    inference(avatar_component_clause,[],[f589])).
% 2.14/0.65  fof(f591,plain,(
% 2.14/0.65    spl3_42 | ~spl3_16),
% 2.14/0.65    inference(avatar_split_clause,[],[f277,f248,f589])).
% 2.14/0.65  fof(f248,plain,(
% 2.14/0.65    spl3_16 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0)))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.14/0.65  fof(f277,plain,(
% 2.14/0.65    ( ! [X0] : (r1_tarski(X0,k2_pre_topc(sK0,X0)) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl3_16),
% 2.14/0.65    inference(resolution,[],[f249,f94])).
% 2.14/0.65  fof(f249,plain,(
% 2.14/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0))) ) | ~spl3_16),
% 2.14/0.65    inference(avatar_component_clause,[],[f248])).
% 2.14/0.65  fof(f489,plain,(
% 2.14/0.65    spl3_36 | ~spl3_1),
% 2.14/0.65    inference(avatar_split_clause,[],[f241,f101,f487])).
% 2.14/0.65  fof(f241,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_tops_1(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X1,sK0)) ) | ~spl3_1),
% 2.14/0.65    inference(resolution,[],[f79,f103])).
% 2.14/0.65  fof(f79,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(X2,X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f34])).
% 2.14/0.65  fof(f34,plain,(
% 2.14/0.65    ! [X0] : (! [X1] : (! [X2] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.65    inference(flattening,[],[f33])).
% 2.14/0.65  fof(f33,plain,(
% 2.14/0.65    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_1(X2,X0) | (~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.65    inference(ennf_transformation,[],[f22])).
% 2.14/0.65  fof(f22,axiom,(
% 2.14/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).
% 2.14/0.65  fof(f459,plain,(
% 2.14/0.65    spl3_34 | ~spl3_1),
% 2.14/0.65    inference(avatar_split_clause,[],[f233,f101,f457])).
% 2.14/0.65  fof(f233,plain,(
% 2.14/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | ~spl3_1),
% 2.14/0.65    inference(resolution,[],[f73,f103])).
% 2.14/0.65  fof(f73,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f28])).
% 2.14/0.65  fof(f28,plain,(
% 2.14/0.65    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.65    inference(ennf_transformation,[],[f16])).
% 2.14/0.65  fof(f16,axiom,(
% 2.14/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 2.14/0.65  fof(f389,plain,(
% 2.14/0.65    spl3_28 | ~spl3_1),
% 2.14/0.65    inference(avatar_split_clause,[],[f201,f101,f387])).
% 2.14/0.65  fof(f201,plain,(
% 2.14/0.65    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)) ) | ~spl3_1),
% 2.14/0.65    inference(resolution,[],[f77,f103])).
% 2.14/0.65  fof(f77,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f58])).
% 2.14/0.65  fof(f373,plain,(
% 2.14/0.65    spl3_24 | ~spl3_21),
% 2.14/0.65    inference(avatar_split_clause,[],[f345,f328,f352])).
% 2.14/0.65  fof(f328,plain,(
% 2.14/0.65    spl3_21 <=> r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 2.14/0.65  fof(f345,plain,(
% 2.14/0.65    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | ~spl3_21),
% 2.14/0.65    inference(subsumption_resolution,[],[f342,f115])).
% 2.14/0.65  fof(f115,plain,(
% 2.14/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.14/0.65    inference(resolution,[],[f93,f70])).
% 2.14/0.65  fof(f342,plain,(
% 2.14/0.65    ~r1_tarski(k1_xboole_0,k1_tops_1(sK0,k1_xboole_0)) | k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | ~spl3_21),
% 2.14/0.65    inference(resolution,[],[f330,f92])).
% 2.14/0.65  fof(f92,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.14/0.65    inference(cnf_transformation,[],[f63])).
% 2.14/0.65  fof(f330,plain,(
% 2.14/0.65    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) | ~spl3_21),
% 2.14/0.65    inference(avatar_component_clause,[],[f328])).
% 2.14/0.65  fof(f349,plain,(
% 2.14/0.65    spl3_23 | ~spl3_1),
% 2.14/0.65    inference(avatar_split_clause,[],[f181,f101,f347])).
% 2.14/0.65  fof(f181,plain,(
% 2.14/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_1),
% 2.14/0.65    inference(resolution,[],[f88,f103])).
% 2.14/0.65  fof(f88,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f43])).
% 2.14/0.65  fof(f43,plain,(
% 2.14/0.65    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.14/0.65    inference(flattening,[],[f42])).
% 2.14/0.65  fof(f42,plain,(
% 2.14/0.65    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.14/0.65    inference(ennf_transformation,[],[f12])).
% 2.14/0.65  fof(f12,axiom,(
% 2.14/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.14/0.65  fof(f331,plain,(
% 2.14/0.65    spl3_21 | ~spl3_17),
% 2.14/0.65    inference(avatar_split_clause,[],[f289,f255,f328])).
% 2.14/0.65  fof(f255,plain,(
% 2.14/0.65    spl3_17 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 2.14/0.65  fof(f289,plain,(
% 2.14/0.65    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) | ~spl3_17),
% 2.14/0.65    inference(resolution,[],[f256,f70])).
% 2.14/0.65  fof(f256,plain,(
% 2.14/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) ) | ~spl3_17),
% 2.14/0.65    inference(avatar_component_clause,[],[f255])).
% 2.14/0.65  fof(f257,plain,(
% 2.14/0.65    spl3_17 | ~spl3_1),
% 2.14/0.65    inference(avatar_split_clause,[],[f168,f101,f255])).
% 2.14/0.65  fof(f168,plain,(
% 2.14/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) ) | ~spl3_1),
% 2.14/0.65    inference(resolution,[],[f72,f103])).
% 2.14/0.65  fof(f72,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f27])).
% 2.14/0.65  fof(f27,plain,(
% 2.14/0.65    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.65    inference(ennf_transformation,[],[f21])).
% 2.14/0.65  fof(f21,axiom,(
% 2.14/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 2.14/0.65  fof(f250,plain,(
% 2.14/0.65    spl3_16 | ~spl3_1),
% 2.14/0.65    inference(avatar_split_clause,[],[f163,f101,f248])).
% 2.14/0.65  fof(f163,plain,(
% 2.14/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0))) ) | ~spl3_1),
% 2.14/0.65    inference(resolution,[],[f71,f103])).
% 2.14/0.65  fof(f71,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f26])).
% 2.14/0.65  fof(f26,plain,(
% 2.14/0.65    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.65    inference(ennf_transformation,[],[f14])).
% 2.14/0.65  fof(f14,axiom,(
% 2.14/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 2.14/0.65  fof(f185,plain,(
% 2.14/0.65    spl3_11 | ~spl3_7),
% 2.14/0.65    inference(avatar_split_clause,[],[f150,f146,f183])).
% 2.14/0.65  fof(f146,plain,(
% 2.14/0.65    spl3_7 <=> r1_tarski(sK2(sK0),u1_struct_0(sK0))),
% 2.14/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.14/0.65  fof(f150,plain,(
% 2.14/0.65    ( ! [X0] : (~r1_tarski(u1_struct_0(sK0),X0) | r1_tarski(sK2(sK0),X0)) ) | ~spl3_7),
% 2.14/0.65    inference(resolution,[],[f148,f97])).
% 2.14/0.65  fof(f97,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f51])).
% 2.14/0.65  fof(f51,plain,(
% 2.14/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.14/0.65    inference(flattening,[],[f50])).
% 2.14/0.65  fof(f50,plain,(
% 2.14/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.14/0.65    inference(ennf_transformation,[],[f3])).
% 2.14/0.65  fof(f3,axiom,(
% 2.14/0.65    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.14/0.65  fof(f148,plain,(
% 2.14/0.65    r1_tarski(sK2(sK0),u1_struct_0(sK0)) | ~spl3_7),
% 2.14/0.65    inference(avatar_component_clause,[],[f146])).
% 2.14/0.65  fof(f149,plain,(
% 2.14/0.65    spl3_7 | ~spl3_1),
% 2.14/0.65    inference(avatar_split_clause,[],[f143,f101,f146])).
% 2.14/0.65  fof(f143,plain,(
% 2.14/0.65    r1_tarski(sK2(sK0),u1_struct_0(sK0)) | ~spl3_1),
% 2.14/0.65    inference(resolution,[],[f134,f103])).
% 2.14/0.65  fof(f134,plain,(
% 2.14/0.65    ( ! [X0] : (~l1_pre_topc(X0) | r1_tarski(sK2(X0),u1_struct_0(X0))) )),
% 2.14/0.65    inference(resolution,[],[f80,f93])).
% 2.14/0.65  fof(f133,plain,(
% 2.14/0.65    ~spl3_4 | ~spl3_5),
% 2.14/0.65    inference(avatar_split_clause,[],[f132,f123,f119])).
% 2.14/0.65  fof(f132,plain,(
% 2.14/0.65    ~v2_tops_1(sK1,sK0) | ~spl3_5),
% 2.14/0.65    inference(subsumption_resolution,[],[f68,f125])).
% 2.14/0.65  fof(f68,plain,(
% 2.14/0.65    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 2.14/0.65    inference(cnf_transformation,[],[f56])).
% 2.14/0.65  fof(f56,plain,(
% 2.14/0.65    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.14/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f53,f55,f54])).
% 2.14/0.65  fof(f54,plain,(
% 2.14/0.65    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.14/0.65    introduced(choice_axiom,[])).
% 2.14/0.65  fof(f55,plain,(
% 2.14/0.65    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.14/0.65    introduced(choice_axiom,[])).
% 2.14/0.65  fof(f53,plain,(
% 2.14/0.65    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.14/0.65    inference(flattening,[],[f52])).
% 2.14/0.65  fof(f52,plain,(
% 2.14/0.65    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.14/0.65    inference(nnf_transformation,[],[f25])).
% 2.14/0.65  fof(f25,plain,(
% 2.14/0.65    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.14/0.65    inference(ennf_transformation,[],[f24])).
% 2.14/0.65  fof(f24,negated_conjecture,(
% 2.14/0.65    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.14/0.65    inference(negated_conjecture,[],[f23])).
% 2.14/0.65  fof(f23,conjecture,(
% 2.14/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.14/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 2.14/0.65  fof(f126,plain,(
% 2.14/0.65    spl3_4 | spl3_5),
% 2.14/0.65    inference(avatar_split_clause,[],[f67,f123,f119])).
% 2.14/0.65  fof(f67,plain,(
% 2.14/0.65    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 2.14/0.65    inference(cnf_transformation,[],[f56])).
% 2.14/0.65  fof(f114,plain,(
% 2.14/0.65    spl3_3),
% 2.14/0.65    inference(avatar_split_clause,[],[f66,f111])).
% 2.14/0.65  fof(f66,plain,(
% 2.14/0.65    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.14/0.65    inference(cnf_transformation,[],[f56])).
% 2.14/0.65  fof(f104,plain,(
% 2.14/0.65    spl3_1),
% 2.14/0.65    inference(avatar_split_clause,[],[f65,f101])).
% 2.14/0.65  fof(f65,plain,(
% 2.14/0.65    l1_pre_topc(sK0)),
% 2.14/0.65    inference(cnf_transformation,[],[f56])).
% 2.14/0.65  % SZS output end Proof for theBenchmark
% 2.14/0.65  % (2248)------------------------------
% 2.14/0.65  % (2248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.65  % (2248)Termination reason: Refutation
% 2.14/0.65  
% 2.14/0.65  % (2248)Memory used [KB]: 7419
% 2.14/0.65  % (2248)Time elapsed: 0.251 s
% 2.14/0.65  % (2248)------------------------------
% 2.14/0.65  % (2248)------------------------------
% 2.14/0.65  % (2245)Success in time 0.3 s
%------------------------------------------------------------------------------
