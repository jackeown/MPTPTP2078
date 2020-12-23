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
% DateTime   : Thu Dec  3 13:19:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 531 expanded)
%              Number of leaves         :   30 ( 208 expanded)
%              Depth                    :   17
%              Number of atoms          :  692 (2090 expanded)
%              Number of equality atoms :   81 ( 287 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f351,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f95,f101,f110,f113,f123,f159,f171,f187,f193,f204,f209,f258,f289,f312,f346])).

fof(f346,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_20
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_20
    | spl3_21 ),
    inference(subsumption_resolution,[],[f344,f311])).

fof(f311,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,o_0_0_xboole_0)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl3_21
  <=> k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f344,plain,
    ( k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,o_0_0_xboole_0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f342,f278])).

fof(f278,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,o_0_0_xboole_0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f239,f268])).

fof(f268,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,o_0_0_xboole_0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f74,f79,f84,f122,f257,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f257,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl3_20
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f122,plain,
    ( r2_hidden(o_0_0_xboole_0,u1_pre_topc(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_9
  <=> r2_hidden(o_0_0_xboole_0,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f84,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f79,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f74,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f239,plain,
    ( k6_tmap_1(sK0,o_0_0_xboole_0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,o_0_0_xboole_0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f173,f233])).

fof(f233,plain,
    ( o_0_0_xboole_0 = sK2(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f232,f186])).

fof(f186,plain,
    ( v3_tops_1(sK2(sK0),sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl3_15
  <=> v3_tops_1(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f232,plain,
    ( ~ v3_tops_1(sK2(sK0),sK0)
    | o_0_0_xboole_0 = sK2(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f230,f203])).

fof(f203,plain,
    ( v3_pre_topc(sK2(sK0),sK0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl3_17
  <=> v3_pre_topc(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f230,plain,
    ( ~ v3_pre_topc(sK2(sK0),sK0)
    | ~ v3_tops_1(sK2(sK0),sK0)
    | o_0_0_xboole_0 = sK2(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(resolution,[],[f143,f170])).

fof(f170,plain,
    ( m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl3_13
  <=> m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_tops_1(X0,sK0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f142,f84])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ v3_tops_1(X0,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl3_2 ),
    inference(resolution,[],[f70,f79])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_tops_1(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | o_0_0_xboole_0 = X1 ) ),
    inference(definition_unfolding,[],[f67,f51])).

fof(f51,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ v3_tops_1(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = X1
          | ~ v3_tops_1(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = X1
          | ~ v3_tops_1(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

fof(f173,plain,
    ( k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f74,f79,f84,f170,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

fof(f342,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_18 ),
    inference(backward_demodulation,[],[f208,f339])).

fof(f339,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f336,f305])).

fof(f305,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f211,f105])).

fof(f105,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_7
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f211,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f116,f94])).

fof(f94,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | r2_hidden(X0,u1_pre_topc(sK0)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f54,f84])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f336,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f154,f94])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f153,f74])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f152,f84])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f62,f79])).

fof(f208,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl3_18
  <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f312,plain,
    ( ~ spl3_21
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_8
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f299,f255,f201,f184,f168,f120,f107,f82,f77,f72,f309])).

fof(f107,plain,
    ( spl3_8
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f299,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,o_0_0_xboole_0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_8
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f108,f278])).

fof(f108,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f289,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9
    | spl3_11
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9
    | spl3_11
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f287,f160])).

fof(f160,plain,
    ( u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f74,f79,f84,f94,f158,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f158,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl3_11
  <=> r2_hidden(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f287,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f283,f277])).

fof(f277,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,o_0_0_xboole_0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f241,f268])).

fof(f241,plain,
    ( k5_tmap_1(sK0,o_0_0_xboole_0) = u1_pre_topc(k6_tmap_1(sK0,o_0_0_xboole_0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f175,f233])).

fof(f175,plain,
    ( k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f74,f79,f84,f170,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f283,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,o_0_0_xboole_0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f192,f280])).

fof(f280,plain,
    ( k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,o_0_0_xboole_0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f109,f278])).

fof(f109,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f192,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl3_16
  <=> k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f258,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f237,f201,f184,f168,f82,f77,f255])).

fof(f237,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f170,f233])).

fof(f209,plain,
    ( spl3_18
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f148,f92,f82,f77,f72,f206])).

fof(f148,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f74,f79,f84,f94,f59])).

fof(f204,plain,
    ( spl3_17
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f177,f168,f98,f82,f77,f201])).

fof(f98,plain,
    ( spl3_6
  <=> v1_xboole_0(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f177,plain,
    ( v3_pre_topc(sK2(sK0),sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f79,f84,f100,f170,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f100,plain,
    ( v1_xboole_0(sK2(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f193,plain,
    ( spl3_16
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f144,f92,f82,f77,f72,f190])).

fof(f144,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f74,f79,f84,f94,f61])).

fof(f187,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f176,f168,f98,f82,f77,f184])).

fof(f176,plain,
    ( v3_tops_1(sK2(sK0),sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f79,f84,f100,f170,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tops_1)).

fof(f171,plain,
    ( spl3_13
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f114,f82,f168])).

fof(f114,plain,
    ( m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f84,f56])).

fof(f56,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_connsp_1)).

fof(f159,plain,
    ( ~ spl3_11
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7 ),
    inference(avatar_split_clause,[],[f117,f103,f92,f82,f156])).

fof(f117,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f84,f104,f94,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f104,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f123,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f115,f82,f77,f120])).

fof(f115,plain,
    ( r2_hidden(o_0_0_xboole_0,u1_pre_topc(sK0))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f79,f84,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(o_0_0_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f64,f51])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).

fof(f113,plain,
    ( ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f112,f107,f103])).

fof(f112,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f111])).

fof(f111,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f50,f109])).

fof(f50,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) )
            & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
            | ~ v3_pre_topc(X1,sK0) )
          & ( k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ( k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          | ~ v3_pre_topc(X1,sK0) )
        & ( k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ v3_pre_topc(X1,X0) )
          & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ v3_pre_topc(X1,X0) )
          & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f110,plain,
    ( spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f49,f107,f103])).

fof(f49,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f101,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f96,f82,f98])).

fof(f96,plain,
    ( v1_xboole_0(sK2(sK0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f84,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v1_xboole_0(sK2(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f48,f92])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f47,f82])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f46,f77])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f45,f72])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:58:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (25742)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (25744)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (25752)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (25756)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (25757)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (25756)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (25743)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (25752)Refutation not found, incomplete strategy% (25752)------------------------------
% 0.21/0.48  % (25752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (25752)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (25752)Memory used [KB]: 10746
% 0.21/0.48  % (25752)Time elapsed: 0.065 s
% 0.21/0.48  % (25752)------------------------------
% 0.21/0.48  % (25752)------------------------------
% 0.21/0.48  % (25741)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (25746)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f351,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f75,f80,f85,f95,f101,f110,f113,f123,f159,f171,f187,f193,f204,f209,f258,f289,f312,f346])).
% 0.21/0.48  fof(f346,plain,(
% 0.21/0.48    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_13 | ~spl3_15 | ~spl3_17 | ~spl3_18 | ~spl3_20 | spl3_21),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f345])).
% 0.21/0.48  fof(f345,plain,(
% 0.21/0.48    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_13 | ~spl3_15 | ~spl3_17 | ~spl3_18 | ~spl3_20 | spl3_21)),
% 0.21/0.48    inference(subsumption_resolution,[],[f344,f311])).
% 0.21/0.48  fof(f311,plain,(
% 0.21/0.48    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,o_0_0_xboole_0) | spl3_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f309])).
% 0.21/0.48  fof(f309,plain,(
% 0.21/0.48    spl3_21 <=> k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,o_0_0_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.48  fof(f344,plain,(
% 0.21/0.48    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,o_0_0_xboole_0) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_13 | ~spl3_15 | ~spl3_17 | ~spl3_18 | ~spl3_20)),
% 0.21/0.48    inference(forward_demodulation,[],[f342,f278])).
% 0.21/0.48  fof(f278,plain,(
% 0.21/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,o_0_0_xboole_0) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_9 | ~spl3_13 | ~spl3_15 | ~spl3_17 | ~spl3_20)),
% 0.21/0.48    inference(backward_demodulation,[],[f239,f268])).
% 0.21/0.48  fof(f268,plain,(
% 0.21/0.48    u1_pre_topc(sK0) = k5_tmap_1(sK0,o_0_0_xboole_0) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_9 | ~spl3_20)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f74,f79,f84,f122,f257,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f255])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    spl3_20 <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    r2_hidden(o_0_0_xboole_0,u1_pre_topc(sK0)) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f120])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    spl3_9 <=> r2_hidden(o_0_0_xboole_0,u1_pre_topc(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    l1_pre_topc(sK0) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl3_3 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    v2_pre_topc(sK0) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl3_2 <=> v2_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ~v2_struct_0(sK0) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl3_1 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    k6_tmap_1(sK0,o_0_0_xboole_0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,o_0_0_xboole_0)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_13 | ~spl3_15 | ~spl3_17)),
% 0.21/0.48    inference(backward_demodulation,[],[f173,f233])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    o_0_0_xboole_0 = sK2(sK0) | (~spl3_2 | ~spl3_3 | ~spl3_13 | ~spl3_15 | ~spl3_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f232,f186])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    v3_tops_1(sK2(sK0),sK0) | ~spl3_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f184])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    spl3_15 <=> v3_tops_1(sK2(sK0),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ~v3_tops_1(sK2(sK0),sK0) | o_0_0_xboole_0 = sK2(sK0) | (~spl3_2 | ~spl3_3 | ~spl3_13 | ~spl3_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f230,f203])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    v3_pre_topc(sK2(sK0),sK0) | ~spl3_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f201])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    spl3_17 <=> v3_pre_topc(sK2(sK0),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    ~v3_pre_topc(sK2(sK0),sK0) | ~v3_tops_1(sK2(sK0),sK0) | o_0_0_xboole_0 = sK2(sK0) | (~spl3_2 | ~spl3_3 | ~spl3_13)),
% 0.21/0.48    inference(resolution,[],[f143,f170])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f168])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    spl3_13 <=> m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v3_tops_1(X0,sK0) | o_0_0_xboole_0 = X0) ) | (~spl3_2 | ~spl3_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f142,f84])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ( ! [X0] : (~v3_tops_1(X0,sK0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | o_0_0_xboole_0 = X0) ) | ~spl3_2),
% 0.21/0.48    inference(resolution,[],[f70,f79])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v3_tops_1(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | o_0_0_xboole_0 = X1) )),
% 0.21/0.48    inference(definition_unfolding,[],[f67,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~v3_tops_1(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_xboole_0 = X1 | ~v3_tops_1(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((k1_xboole_0 = X1 | (~v3_tops_1(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0))) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_13)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f74,f79,f84,f170,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).
% 0.21/0.48  fof(f342,plain,(
% 0.21/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_18)),
% 0.21/0.48    inference(backward_demodulation,[],[f208,f339])).
% 0.21/0.48  fof(f339,plain,(
% 0.21/0.48    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f336,f305])).
% 0.21/0.48  fof(f305,plain,(
% 0.21/0.48    r2_hidden(sK1,u1_pre_topc(sK0)) | (~spl3_3 | ~spl3_5 | ~spl3_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f211,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    v3_pre_topc(sK1,sK0) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl3_7 <=> v3_pre_topc(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    ~v3_pre_topc(sK1,sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | (~spl3_3 | ~spl3_5)),
% 0.21/0.48    inference(resolution,[],[f116,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | r2_hidden(X0,u1_pre_topc(sK0))) ) | ~spl3_3),
% 0.21/0.48    inference(resolution,[],[f54,f84])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.21/0.48  fof(f336,plain,(
% 0.21/0.48    ~r2_hidden(sK1,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5)),
% 0.21/0.48    inference(resolution,[],[f154,f94])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f153,f74])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | v2_struct_0(sK0)) ) | (~spl3_2 | ~spl3_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f152,f84])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | v2_struct_0(sK0)) ) | ~spl3_2),
% 0.21/0.48    inference(resolution,[],[f62,f79])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) | ~spl3_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f206])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    spl3_18 <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.48  fof(f312,plain,(
% 0.21/0.48    ~spl3_21 | spl3_1 | ~spl3_2 | ~spl3_3 | spl3_8 | ~spl3_9 | ~spl3_13 | ~spl3_15 | ~spl3_17 | ~spl3_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f299,f255,f201,f184,f168,f120,f107,f82,f77,f72,f309])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl3_8 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f299,plain,(
% 0.21/0.48    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,o_0_0_xboole_0) | (spl3_1 | ~spl3_2 | ~spl3_3 | spl3_8 | ~spl3_9 | ~spl3_13 | ~spl3_15 | ~spl3_17 | ~spl3_20)),
% 0.21/0.48    inference(forward_demodulation,[],[f108,f278])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f107])).
% 0.21/0.48  fof(f289,plain,(
% 0.21/0.48    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_8 | ~spl3_9 | spl3_11 | ~spl3_13 | ~spl3_15 | ~spl3_16 | ~spl3_17 | ~spl3_20),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f288])).
% 0.21/0.48  fof(f288,plain,(
% 0.21/0.48    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_8 | ~spl3_9 | spl3_11 | ~spl3_13 | ~spl3_15 | ~spl3_16 | ~spl3_17 | ~spl3_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f287,f160])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | spl3_11)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f74,f79,f84,f94,f158,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0,X1] : (u1_pre_topc(X0) != k5_tmap_1(X0,X1) | r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f44])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ~r2_hidden(sK1,u1_pre_topc(sK0)) | spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f156])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    spl3_11 <=> r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f287,plain,(
% 0.21/0.48    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_8 | ~spl3_9 | ~spl3_13 | ~spl3_15 | ~spl3_16 | ~spl3_17 | ~spl3_20)),
% 0.21/0.48    inference(forward_demodulation,[],[f283,f277])).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,o_0_0_xboole_0)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_9 | ~spl3_13 | ~spl3_15 | ~spl3_17 | ~spl3_20)),
% 0.21/0.48    inference(backward_demodulation,[],[f241,f268])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    k5_tmap_1(sK0,o_0_0_xboole_0) = u1_pre_topc(k6_tmap_1(sK0,o_0_0_xboole_0)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_13 | ~spl3_15 | ~spl3_17)),
% 0.21/0.48    inference(backward_demodulation,[],[f175,f233])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0))) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_13)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f74,f79,f84,f170,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.21/0.48  fof(f283,plain,(
% 0.21/0.48    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,o_0_0_xboole_0)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_8 | ~spl3_9 | ~spl3_13 | ~spl3_15 | ~spl3_16 | ~spl3_17 | ~spl3_20)),
% 0.21/0.48    inference(backward_demodulation,[],[f192,f280])).
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,o_0_0_xboole_0) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_8 | ~spl3_9 | ~spl3_13 | ~spl3_15 | ~spl3_17 | ~spl3_20)),
% 0.21/0.48    inference(backward_demodulation,[],[f109,f278])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f107])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) | ~spl3_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f190])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    spl3_16 <=> k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    spl3_20 | ~spl3_2 | ~spl3_3 | ~spl3_13 | ~spl3_15 | ~spl3_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f237,f201,f184,f168,f82,f77,f255])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3 | ~spl3_13 | ~spl3_15 | ~spl3_17)),
% 0.21/0.48    inference(backward_demodulation,[],[f170,f233])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    spl3_18 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f148,f92,f82,f77,f72,f206])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f74,f79,f84,f94,f59])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    spl3_17 | ~spl3_2 | ~spl3_3 | ~spl3_6 | ~spl3_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f177,f168,f98,f82,f77,f201])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl3_6 <=> v1_xboole_0(sK2(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    v3_pre_topc(sK2(sK0),sK0) | (~spl3_2 | ~spl3_3 | ~spl3_6 | ~spl3_13)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f79,f84,f100,f170,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    v1_xboole_0(sK2(sK0)) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f98])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    spl3_16 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f144,f92,f82,f77,f72,f190])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f74,f79,f84,f94,f61])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    spl3_15 | ~spl3_2 | ~spl3_3 | ~spl3_6 | ~spl3_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f176,f168,f98,f82,f77,f184])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    v3_tops_1(sK2(sK0),sK0) | (~spl3_2 | ~spl3_3 | ~spl3_6 | ~spl3_13)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f79,f84,f100,f170,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_tops_1(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tops_1)).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    spl3_13 | ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f114,f82,f168])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f84,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_connsp_1)).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    ~spl3_11 | ~spl3_3 | ~spl3_5 | spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f117,f103,f92,f82,f156])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ~r2_hidden(sK1,u1_pre_topc(sK0)) | (~spl3_3 | ~spl3_5 | spl3_7)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f84,f104,f94,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ~v3_pre_topc(sK1,sK0) | spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f103])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    spl3_9 | ~spl3_2 | ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f115,f82,f77,f120])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    r2_hidden(o_0_0_xboole_0,u1_pre_topc(sK0)) | (~spl3_2 | ~spl3_3)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f79,f84,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(o_0_0_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f64,f51])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => r2_hidden(k1_xboole_0,u1_pre_topc(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ~spl3_7 | ~spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f112,f107,f103])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ~v3_pre_topc(sK1,sK0) | ~spl3_8),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f111])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~spl3_8),
% 0.21/0.48    inference(backward_demodulation,[],[f50,f109])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~v3_pre_topc(X1,sK0)) & (k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ? [X1] : ((k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~v3_pre_topc(X1,sK0)) & (k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f14])).
% 0.21/0.48  fof(f14,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl3_7 | spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f49,f107,f103])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl3_6 | ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f96,f82,f98])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    v1_xboole_0(sK2(sK0)) | ~spl3_3),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f84,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(sK2(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f43])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f48,f92])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f47,f82])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f46,f77])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f45,f72])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (25755)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (25756)------------------------------
% 0.21/0.48  % (25756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (25756)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (25756)Memory used [KB]: 10746
% 0.21/0.48  % (25756)Time elapsed: 0.067 s
% 0.21/0.48  % (25756)------------------------------
% 0.21/0.48  % (25756)------------------------------
% 0.21/0.49  % (25740)Success in time 0.123 s
%------------------------------------------------------------------------------
