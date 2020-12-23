%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 175 expanded)
%              Number of leaves         :   27 (  81 expanded)
%              Depth                    :    7
%              Number of atoms          :  302 ( 530 expanded)
%              Number of equality atoms :   50 (  74 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f56,f64,f68,f72,f76,f80,f85,f103,f113,f123,f134,f160,f171,f179,f182])).

fof(f182,plain,
    ( ~ spl2_8
    | spl2_18
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl2_8
    | spl2_18
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f180,f122])).

fof(f122,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_18 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl2_18
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f180,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_8
    | ~ spl2_26 ),
    inference(superposition,[],[f67,f177])).

fof(f177,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl2_26
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f67,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_8
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f179,plain,
    ( spl2_26
    | ~ spl2_12
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f173,f168,f83,f175])).

fof(f83,plain,
    ( spl2_12
  <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f168,plain,
    ( spl2_25
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f173,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_12
    | ~ spl2_25 ),
    inference(superposition,[],[f84,f170])).

fof(f170,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f168])).

fof(f84,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f171,plain,
    ( spl2_25
    | ~ spl2_19
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f165,f157,f131,f168])).

fof(f131,plain,
    ( spl2_19
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f157,plain,
    ( spl2_23
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f165,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_19
    | ~ spl2_23 ),
    inference(backward_demodulation,[],[f133,f159])).

fof(f159,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f157])).

fof(f133,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f131])).

fof(f160,plain,
    ( spl2_23
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f155,f110,f101,f49,f44,f157])).

fof(f44,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f49,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f101,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f110,plain,
    ( spl2_16
  <=> sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f155,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f154,f112])).

fof(f112,plain,
    ( sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f110])).

fof(f154,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f151,f51])).

fof(f51,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f151,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(resolution,[],[f102,f46])).

fof(f46,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f134,plain,
    ( spl2_19
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f129,f54,f49,f44,f131])).

fof(f54,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f129,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f126,f51])).

fof(f126,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(resolution,[],[f55,f46])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f123,plain,
    ( ~ spl2_18
    | spl2_1
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f118,f110,f34,f120])).

fof(f34,plain,
    ( spl2_1
  <=> r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f118,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_1
    | ~ spl2_16 ),
    inference(backward_demodulation,[],[f36,f112])).

fof(f36,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f113,plain,
    ( spl2_16
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f108,f62,f49,f44,f39,f110])).

fof(f39,plain,
    ( spl2_2
  <=> v5_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f62,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
        | ~ v5_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f108,plain,
    ( sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f107,f51])).

fof(f107,plain,
    ( sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f104,f41])).

fof(f41,plain,
    ( v5_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f104,plain,
    ( ~ v5_tops_1(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f63,f46])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v5_tops_1(X1,X0)
        | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
        | ~ l1_pre_topc(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f103,plain,
    ( spl2_15
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f93,f74,f70,f101])).

fof(f70,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f74,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(resolution,[],[f75,f71])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f85,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f81,f78,f44,f83])).

fof(f78,plain,
    ( spl2_11
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f81,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(resolution,[],[f79,f46])).

fof(f79,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f76,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f72,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f68,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f64,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(f56,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f52,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
            & v5_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
          & v5_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
        & v5_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
      & v5_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

fof(f47,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f24,f39])).

fof(f24,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f25,f34])).

fof(f25,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.41  % (9981)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.41  % (9975)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.41  % (9981)Refutation found. Thanks to Tanya!
% 0.22/0.41  % SZS status Theorem for theBenchmark
% 0.22/0.41  % SZS output start Proof for theBenchmark
% 0.22/0.41  fof(f183,plain,(
% 0.22/0.41    $false),
% 0.22/0.41    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f56,f64,f68,f72,f76,f80,f85,f103,f113,f123,f134,f160,f171,f179,f182])).
% 0.22/0.41  fof(f182,plain,(
% 0.22/0.41    ~spl2_8 | spl2_18 | ~spl2_26),
% 0.22/0.41    inference(avatar_contradiction_clause,[],[f181])).
% 0.22/0.41  fof(f181,plain,(
% 0.22/0.41    $false | (~spl2_8 | spl2_18 | ~spl2_26)),
% 0.22/0.41    inference(subsumption_resolution,[],[f180,f122])).
% 0.22/0.41  fof(f122,plain,(
% 0.22/0.41    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_18),
% 0.22/0.41    inference(avatar_component_clause,[],[f120])).
% 0.22/0.41  fof(f120,plain,(
% 0.22/0.41    spl2_18 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.41  fof(f180,plain,(
% 0.22/0.41    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_8 | ~spl2_26)),
% 0.22/0.41    inference(superposition,[],[f67,f177])).
% 0.22/0.41  fof(f177,plain,(
% 0.22/0.41    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_26),
% 0.22/0.41    inference(avatar_component_clause,[],[f175])).
% 0.22/0.41  fof(f175,plain,(
% 0.22/0.41    spl2_26 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.41  fof(f67,plain,(
% 0.22/0.41    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_8),
% 0.22/0.41    inference(avatar_component_clause,[],[f66])).
% 0.22/0.41  fof(f66,plain,(
% 0.22/0.41    spl2_8 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.41  fof(f179,plain,(
% 0.22/0.41    spl2_26 | ~spl2_12 | ~spl2_25),
% 0.22/0.41    inference(avatar_split_clause,[],[f173,f168,f83,f175])).
% 0.22/0.41  fof(f83,plain,(
% 0.22/0.41    spl2_12 <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.41  fof(f168,plain,(
% 0.22/0.41    spl2_25 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.22/0.41  fof(f173,plain,(
% 0.22/0.41    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_12 | ~spl2_25)),
% 0.22/0.41    inference(superposition,[],[f84,f170])).
% 0.22/0.41  fof(f170,plain,(
% 0.22/0.41    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_25),
% 0.22/0.41    inference(avatar_component_clause,[],[f168])).
% 0.22/0.41  fof(f84,plain,(
% 0.22/0.41    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl2_12),
% 0.22/0.41    inference(avatar_component_clause,[],[f83])).
% 0.22/0.41  fof(f171,plain,(
% 0.22/0.41    spl2_25 | ~spl2_19 | ~spl2_23),
% 0.22/0.41    inference(avatar_split_clause,[],[f165,f157,f131,f168])).
% 0.22/0.41  fof(f131,plain,(
% 0.22/0.41    spl2_19 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.41  fof(f157,plain,(
% 0.22/0.41    spl2_23 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.41  fof(f165,plain,(
% 0.22/0.41    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_19 | ~spl2_23)),
% 0.22/0.41    inference(backward_demodulation,[],[f133,f159])).
% 0.22/0.41  fof(f159,plain,(
% 0.22/0.41    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_23),
% 0.22/0.41    inference(avatar_component_clause,[],[f157])).
% 0.22/0.41  fof(f133,plain,(
% 0.22/0.41    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_19),
% 0.22/0.41    inference(avatar_component_clause,[],[f131])).
% 0.22/0.41  fof(f160,plain,(
% 0.22/0.41    spl2_23 | ~spl2_3 | ~spl2_4 | ~spl2_15 | ~spl2_16),
% 0.22/0.41    inference(avatar_split_clause,[],[f155,f110,f101,f49,f44,f157])).
% 0.22/0.41  fof(f44,plain,(
% 0.22/0.41    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.41  fof(f49,plain,(
% 0.22/0.41    spl2_4 <=> l1_pre_topc(sK0)),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.41  fof(f101,plain,(
% 0.22/0.41    spl2_15 <=> ! [X1,X0] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.41  fof(f110,plain,(
% 0.22/0.41    spl2_16 <=> sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.41  fof(f155,plain,(
% 0.22/0.41    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_4 | ~spl2_15 | ~spl2_16)),
% 0.22/0.41    inference(forward_demodulation,[],[f154,f112])).
% 0.22/0.41  fof(f112,plain,(
% 0.22/0.41    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | ~spl2_16),
% 0.22/0.41    inference(avatar_component_clause,[],[f110])).
% 0.22/0.41  fof(f154,plain,(
% 0.22/0.41    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_4 | ~spl2_15)),
% 0.22/0.41    inference(subsumption_resolution,[],[f151,f51])).
% 0.22/0.41  fof(f51,plain,(
% 0.22/0.41    l1_pre_topc(sK0) | ~spl2_4),
% 0.22/0.41    inference(avatar_component_clause,[],[f49])).
% 0.22/0.41  fof(f151,plain,(
% 0.22/0.41    ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_15)),
% 0.22/0.41    inference(resolution,[],[f102,f46])).
% 0.22/0.41  fof(f46,plain,(
% 0.22/0.41    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.22/0.41    inference(avatar_component_clause,[],[f44])).
% 0.22/0.41  fof(f102,plain,(
% 0.22/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) ) | ~spl2_15),
% 0.22/0.41    inference(avatar_component_clause,[],[f101])).
% 0.22/0.41  fof(f134,plain,(
% 0.22/0.41    spl2_19 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 0.22/0.41    inference(avatar_split_clause,[],[f129,f54,f49,f44,f131])).
% 0.22/0.41  fof(f54,plain,(
% 0.22/0.41    spl2_5 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.41  fof(f129,plain,(
% 0.22/0.41    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.22/0.41    inference(subsumption_resolution,[],[f126,f51])).
% 0.22/0.41  fof(f126,plain,(
% 0.22/0.41    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_5)),
% 0.22/0.41    inference(resolution,[],[f55,f46])).
% 0.22/0.41  fof(f55,plain,(
% 0.22/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) ) | ~spl2_5),
% 0.22/0.41    inference(avatar_component_clause,[],[f54])).
% 0.22/0.41  fof(f123,plain,(
% 0.22/0.41    ~spl2_18 | spl2_1 | ~spl2_16),
% 0.22/0.41    inference(avatar_split_clause,[],[f118,f110,f34,f120])).
% 0.22/0.41  fof(f34,plain,(
% 0.22/0.41    spl2_1 <=> r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.41  fof(f118,plain,(
% 0.22/0.41    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | (spl2_1 | ~spl2_16)),
% 0.22/0.41    inference(backward_demodulation,[],[f36,f112])).
% 0.22/0.41  fof(f36,plain,(
% 0.22/0.41    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | spl2_1),
% 0.22/0.41    inference(avatar_component_clause,[],[f34])).
% 0.22/0.41  fof(f113,plain,(
% 0.22/0.41    spl2_16 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_7),
% 0.22/0.41    inference(avatar_split_clause,[],[f108,f62,f49,f44,f39,f110])).
% 0.22/0.41  fof(f39,plain,(
% 0.22/0.41    spl2_2 <=> v5_tops_1(sK1,sK0)),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.41  fof(f62,plain,(
% 0.22/0.41    spl2_7 <=> ! [X1,X0] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.41  fof(f108,plain,(
% 0.22/0.41    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_7)),
% 0.22/0.41    inference(subsumption_resolution,[],[f107,f51])).
% 0.22/0.41  fof(f107,plain,(
% 0.22/0.41    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | (~spl2_2 | ~spl2_3 | ~spl2_7)),
% 0.22/0.41    inference(subsumption_resolution,[],[f104,f41])).
% 0.22/0.41  fof(f41,plain,(
% 0.22/0.41    v5_tops_1(sK1,sK0) | ~spl2_2),
% 0.22/0.41    inference(avatar_component_clause,[],[f39])).
% 0.22/0.41  fof(f104,plain,(
% 0.22/0.41    ~v5_tops_1(sK1,sK0) | sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_7)),
% 0.22/0.41    inference(resolution,[],[f63,f46])).
% 0.22/0.41  fof(f63,plain,(
% 0.22/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~l1_pre_topc(X0)) ) | ~spl2_7),
% 0.22/0.41    inference(avatar_component_clause,[],[f62])).
% 0.22/0.41  fof(f103,plain,(
% 0.22/0.41    spl2_15 | ~spl2_9 | ~spl2_10),
% 0.22/0.41    inference(avatar_split_clause,[],[f93,f74,f70,f101])).
% 0.22/0.41  fof(f70,plain,(
% 0.22/0.41    spl2_9 <=> ! [X1,X0] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.41  fof(f74,plain,(
% 0.22/0.41    spl2_10 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.41  fof(f93,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl2_9 | ~spl2_10)),
% 0.22/0.41    inference(duplicate_literal_removal,[],[f92])).
% 0.22/0.41  fof(f92,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | (~spl2_9 | ~spl2_10)),
% 0.22/0.41    inference(resolution,[],[f75,f71])).
% 0.22/0.41  fof(f71,plain,(
% 0.22/0.41    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_9),
% 0.22/0.41    inference(avatar_component_clause,[],[f70])).
% 0.22/0.41  fof(f75,plain,(
% 0.22/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) ) | ~spl2_10),
% 0.22/0.41    inference(avatar_component_clause,[],[f74])).
% 0.22/0.41  fof(f85,plain,(
% 0.22/0.41    spl2_12 | ~spl2_3 | ~spl2_11),
% 0.22/0.41    inference(avatar_split_clause,[],[f81,f78,f44,f83])).
% 0.22/0.41  fof(f78,plain,(
% 0.22/0.41    spl2_11 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.41  fof(f81,plain,(
% 0.22/0.41    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | (~spl2_3 | ~spl2_11)),
% 0.22/0.41    inference(resolution,[],[f79,f46])).
% 0.22/0.41  fof(f79,plain,(
% 0.22/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) ) | ~spl2_11),
% 0.22/0.41    inference(avatar_component_clause,[],[f78])).
% 0.22/0.41  fof(f80,plain,(
% 0.22/0.41    spl2_11),
% 0.22/0.41    inference(avatar_split_clause,[],[f32,f78])).
% 0.22/0.41  fof(f32,plain,(
% 0.22/0.41    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.41    inference(cnf_transformation,[],[f17])).
% 0.22/0.41  fof(f17,plain,(
% 0.22/0.41    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.41    inference(ennf_transformation,[],[f2])).
% 0.22/0.41  fof(f2,axiom,(
% 0.22/0.41    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.41  fof(f76,plain,(
% 0.22/0.41    spl2_10),
% 0.22/0.41    inference(avatar_split_clause,[],[f31,f74])).
% 0.22/0.41  fof(f31,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f16])).
% 0.22/0.41  fof(f16,plain,(
% 0.22/0.41    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.41    inference(flattening,[],[f15])).
% 0.22/0.41  fof(f15,plain,(
% 0.22/0.41    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.41    inference(ennf_transformation,[],[f3])).
% 0.22/0.41  fof(f3,axiom,(
% 0.22/0.41    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 0.22/0.41  fof(f72,plain,(
% 0.22/0.41    spl2_9),
% 0.22/0.41    inference(avatar_split_clause,[],[f30,f70])).
% 0.22/0.41  fof(f30,plain,(
% 0.22/0.41    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f14])).
% 0.22/0.41  fof(f14,plain,(
% 0.22/0.41    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.41    inference(flattening,[],[f13])).
% 0.22/0.41  fof(f13,plain,(
% 0.22/0.41    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.41    inference(ennf_transformation,[],[f5])).
% 0.22/0.41  fof(f5,axiom,(
% 0.22/0.41    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.22/0.41  fof(f68,plain,(
% 0.22/0.41    spl2_8),
% 0.22/0.41    inference(avatar_split_clause,[],[f29,f66])).
% 0.22/0.41  fof(f29,plain,(
% 0.22/0.41    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f1])).
% 0.22/0.41  fof(f1,axiom,(
% 0.22/0.41    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.41  fof(f64,plain,(
% 0.22/0.41    spl2_7),
% 0.22/0.41    inference(avatar_split_clause,[],[f27,f62])).
% 0.22/0.41  fof(f27,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f21])).
% 0.22/0.41  fof(f21,plain,(
% 0.22/0.41    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.41    inference(nnf_transformation,[],[f12])).
% 0.22/0.41  fof(f12,plain,(
% 0.22/0.41    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.41    inference(ennf_transformation,[],[f4])).
% 0.22/0.41  fof(f4,axiom,(
% 0.22/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).
% 0.22/0.41  fof(f56,plain,(
% 0.22/0.41    spl2_5),
% 0.22/0.41    inference(avatar_split_clause,[],[f26,f54])).
% 0.22/0.41  fof(f26,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f11])).
% 0.22/0.41  fof(f11,plain,(
% 0.22/0.41    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.41    inference(ennf_transformation,[],[f6])).
% 0.22/0.41  fof(f6,axiom,(
% 0.22/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.22/0.41  fof(f52,plain,(
% 0.22/0.41    spl2_4),
% 0.22/0.41    inference(avatar_split_clause,[],[f22,f49])).
% 0.22/0.41  fof(f22,plain,(
% 0.22/0.41    l1_pre_topc(sK0)),
% 0.22/0.41    inference(cnf_transformation,[],[f20])).
% 0.22/0.41  fof(f20,plain,(
% 0.22/0.41    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f19,f18])).
% 0.22/0.41  fof(f18,plain,(
% 0.22/0.41    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.41    introduced(choice_axiom,[])).
% 0.22/0.41  fof(f19,plain,(
% 0.22/0.41    ? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.41    introduced(choice_axiom,[])).
% 0.22/0.41  fof(f10,plain,(
% 0.22/0.41    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.41    inference(flattening,[],[f9])).
% 0.22/0.41  fof(f9,plain,(
% 0.22/0.41    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.41    inference(ennf_transformation,[],[f8])).
% 0.22/0.41  fof(f8,negated_conjecture,(
% 0.22/0.41    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 0.22/0.41    inference(negated_conjecture,[],[f7])).
% 0.22/0.41  fof(f7,conjecture,(
% 0.22/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    spl2_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f23,f44])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.42    inference(cnf_transformation,[],[f20])).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    spl2_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f24,f39])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    v5_tops_1(sK1,sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f20])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    ~spl2_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f25,f34])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 0.22/0.42    inference(cnf_transformation,[],[f20])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (9981)------------------------------
% 0.22/0.42  % (9981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (9981)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (9981)Memory used [KB]: 6140
% 0.22/0.42  % (9981)Time elapsed: 0.007 s
% 0.22/0.42  % (9981)------------------------------
% 0.22/0.42  % (9981)------------------------------
% 0.22/0.42  % (9970)Success in time 0.06 s
%------------------------------------------------------------------------------
