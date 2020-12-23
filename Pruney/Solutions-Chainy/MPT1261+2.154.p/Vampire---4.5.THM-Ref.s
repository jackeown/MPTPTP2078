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
% DateTime   : Thu Dec  3 13:12:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 370 expanded)
%              Number of leaves         :   53 ( 169 expanded)
%              Depth                    :   10
%              Number of atoms          :  649 (1225 expanded)
%              Number of equality atoms :  131 ( 264 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f653,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f83,f88,f92,f96,f100,f116,f126,f128,f132,f136,f143,f150,f157,f163,f181,f190,f195,f228,f237,f292,f331,f345,f353,f358,f367,f415,f464,f498,f523,f539,f552,f570,f596,f603,f636,f652])).

fof(f652,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | spl2_12
    | ~ spl2_23
    | ~ spl2_56 ),
    inference(avatar_contradiction_clause,[],[f651])).

fof(f651,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5
    | spl2_12
    | ~ spl2_23
    | ~ spl2_56 ),
    inference(subsumption_resolution,[],[f650,f69])).

fof(f69,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f650,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_5
    | spl2_12
    | ~ spl2_23
    | ~ spl2_56 ),
    inference(subsumption_resolution,[],[f649,f74])).

fof(f74,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f649,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_5
    | spl2_12
    | ~ spl2_23
    | ~ spl2_56 ),
    inference(subsumption_resolution,[],[f648,f87])).

fof(f87,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f648,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl2_12
    | ~ spl2_23
    | ~ spl2_56 ),
    inference(subsumption_resolution,[],[f640,f120])).

fof(f120,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl2_12
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f640,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_23
    | ~ spl2_56 ),
    inference(superposition,[],[f180,f366])).

fof(f366,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl2_56
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f636,plain,
    ( spl2_56
    | ~ spl2_5
    | ~ spl2_18
    | ~ spl2_55
    | ~ spl2_73
    | ~ spl2_87
    | ~ spl2_91 ),
    inference(avatar_split_clause,[],[f628,f568,f550,f462,f355,f154,f85,f364])).

fof(f154,plain,
    ( spl2_18
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f355,plain,
    ( spl2_55
  <=> sK1 = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f462,plain,
    ( spl2_73
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).

fof(f550,plain,
    ( spl2_87
  <=> ! [X1,X2] :
        ( k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X1,X1,X2)
        | ~ r1_tarski(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).

fof(f568,plain,
    ( spl2_91
  <=> ! [X1] :
        ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X1)) = k3_tarski(k1_enumset1(sK1,sK1,k2_tops_1(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_91])])).

fof(f628,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_5
    | ~ spl2_18
    | ~ spl2_55
    | ~ spl2_73
    | ~ spl2_87
    | ~ spl2_91 ),
    inference(forward_demodulation,[],[f627,f357])).

fof(f357,plain,
    ( sK1 = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f355])).

fof(f627,plain,
    ( k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | ~ spl2_5
    | ~ spl2_18
    | ~ spl2_73
    | ~ spl2_87
    | ~ spl2_91 ),
    inference(forward_demodulation,[],[f621,f620])).

fof(f620,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k1_enumset1(sK1,sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_5
    | ~ spl2_73
    | ~ spl2_91 ),
    inference(forward_demodulation,[],[f573,f467])).

fof(f467,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_73 ),
    inference(resolution,[],[f463,f87])).

fof(f463,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_73 ),
    inference(avatar_component_clause,[],[f462])).

fof(f573,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_5
    | ~ spl2_91 ),
    inference(resolution,[],[f569,f87])).

fof(f569,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X1)) = k3_tarski(k1_enumset1(sK1,sK1,k2_tops_1(sK0,X1))) )
    | ~ spl2_91 ),
    inference(avatar_component_clause,[],[f568])).

fof(f621,plain,
    ( k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_18
    | ~ spl2_87 ),
    inference(resolution,[],[f156,f551])).

fof(f551,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X2,X1)
        | k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X1,X1,X2) )
    | ~ spl2_87 ),
    inference(avatar_component_clause,[],[f550])).

fof(f156,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f154])).

fof(f603,plain,
    ( ~ spl2_5
    | spl2_13
    | ~ spl2_56
    | ~ spl2_95 ),
    inference(avatar_contradiction_clause,[],[f602])).

fof(f602,plain,
    ( $false
    | ~ spl2_5
    | spl2_13
    | ~ spl2_56
    | ~ spl2_95 ),
    inference(subsumption_resolution,[],[f601,f124])).

fof(f124,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl2_13
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f601,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_56
    | ~ spl2_95 ),
    inference(forward_demodulation,[],[f599,f366])).

fof(f599,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_95 ),
    inference(resolution,[],[f595,f87])).

fof(f595,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_95 ),
    inference(avatar_component_clause,[],[f594])).

fof(f594,plain,
    ( spl2_95
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).

fof(f596,plain,
    ( spl2_95
    | ~ spl2_2
    | ~ spl2_84 ),
    inference(avatar_split_clause,[],[f592,f537,f72,f594])).

fof(f537,plain,
    ( spl2_84
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_84])])).

fof(f592,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_84 ),
    inference(resolution,[],[f538,f74])).

fof(f538,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) )
    | ~ spl2_84 ),
    inference(avatar_component_clause,[],[f537])).

fof(f570,plain,
    ( spl2_91
    | ~ spl2_26
    | ~ spl2_78 ),
    inference(avatar_split_clause,[],[f502,f496,f193,f568])).

fof(f193,plain,
    ( spl2_26
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f496,plain,
    ( spl2_78
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X5) = k3_tarski(k1_enumset1(sK1,sK1,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f502,plain,
    ( ! [X1] :
        ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X1)) = k3_tarski(k1_enumset1(sK1,sK1,k2_tops_1(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_26
    | ~ spl2_78 ),
    inference(resolution,[],[f497,f194])).

fof(f194,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f193])).

fof(f497,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X5) = k3_tarski(k1_enumset1(sK1,sK1,X5)) )
    | ~ spl2_78 ),
    inference(avatar_component_clause,[],[f496])).

fof(f552,plain,
    ( spl2_87
    | ~ spl2_7
    | ~ spl2_82 ),
    inference(avatar_split_clause,[],[f525,f521,f94,f550])).

fof(f94,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f521,plain,
    ( spl2_82
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k4_subset_1(X1,X1,X0) = k3_tarski(k1_enumset1(X1,X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).

fof(f525,plain,
    ( ! [X2,X1] :
        ( k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X1,X1,X2)
        | ~ r1_tarski(X2,X1) )
    | ~ spl2_7
    | ~ spl2_82 ),
    inference(resolution,[],[f522,f95])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f522,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k4_subset_1(X1,X1,X0) = k3_tarski(k1_enumset1(X1,X1,X0)) )
    | ~ spl2_82 ),
    inference(avatar_component_clause,[],[f521])).

fof(f539,plain,(
    spl2_84 ),
    inference(avatar_split_clause,[],[f49,f537])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f523,plain,
    ( spl2_82
    | ~ spl2_4
    | ~ spl2_64 ),
    inference(avatar_split_clause,[],[f471,f413,f81,f521])).

fof(f81,plain,
    ( spl2_4
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f413,plain,
    ( spl2_64
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).

fof(f471,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k4_subset_1(X1,X1,X0) = k3_tarski(k1_enumset1(X1,X1,X0)) )
    | ~ spl2_4
    | ~ spl2_64 ),
    inference(resolution,[],[f414,f82])).

fof(f82,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f414,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) )
    | ~ spl2_64 ),
    inference(avatar_component_clause,[],[f413])).

fof(f498,plain,
    ( spl2_78
    | ~ spl2_5
    | ~ spl2_64 ),
    inference(avatar_split_clause,[],[f473,f413,f85,f496])).

fof(f473,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X5) = k3_tarski(k1_enumset1(sK1,sK1,X5)) )
    | ~ spl2_5
    | ~ spl2_64 ),
    inference(resolution,[],[f414,f87])).

fof(f464,plain,
    ( spl2_73
    | ~ spl2_2
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f460,f351,f72,f462])).

fof(f351,plain,
    ( spl2_54
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f460,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_54 ),
    inference(resolution,[],[f352,f74])).

fof(f352,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) )
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f351])).

fof(f415,plain,(
    spl2_64 ),
    inference(avatar_split_clause,[],[f63,f413])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f60,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f367,plain,
    ( spl2_56
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f362,f235,f119,f85,f364])).

fof(f235,plain,
    ( spl2_34
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f362,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f361,f87])).

fof(f361,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_12
    | ~ spl2_34 ),
    inference(resolution,[],[f121,f236])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f235])).

fof(f121,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f358,plain,
    ( spl2_55
    | ~ spl2_18
    | ~ spl2_19
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f349,f343,f160,f154,f355])).

fof(f160,plain,
    ( spl2_19
  <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f343,plain,
    ( spl2_53
  <=> ! [X1,X2] :
        ( k4_subset_1(X1,X2,X1) = k4_subset_1(X1,X1,X2)
        | ~ r1_tarski(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f349,plain,
    ( sK1 = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_18
    | ~ spl2_19
    | ~ spl2_53 ),
    inference(forward_demodulation,[],[f347,f162])).

fof(f162,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f160])).

fof(f347,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_18
    | ~ spl2_53 ),
    inference(resolution,[],[f344,f156])).

fof(f344,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X2,X1)
        | k4_subset_1(X1,X2,X1) = k4_subset_1(X1,X1,X2) )
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f343])).

fof(f353,plain,(
    spl2_54 ),
    inference(avatar_split_clause,[],[f48,f351])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f345,plain,
    ( spl2_53
    | ~ spl2_7
    | ~ spl2_51 ),
    inference(avatar_split_clause,[],[f333,f329,f94,f343])).

fof(f329,plain,
    ( spl2_51
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k4_subset_1(X1,X1,X0) = k4_subset_1(X1,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f333,plain,
    ( ! [X2,X1] :
        ( k4_subset_1(X1,X2,X1) = k4_subset_1(X1,X1,X2)
        | ~ r1_tarski(X2,X1) )
    | ~ spl2_7
    | ~ spl2_51 ),
    inference(resolution,[],[f330,f95])).

fof(f330,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k4_subset_1(X1,X1,X0) = k4_subset_1(X1,X0,X1) )
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f329])).

fof(f331,plain,
    ( spl2_51
    | ~ spl2_4
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f324,f290,f81,f329])).

fof(f290,plain,
    ( spl2_44
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f324,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k4_subset_1(X1,X1,X0) = k4_subset_1(X1,X0,X1) )
    | ~ spl2_4
    | ~ spl2_44 ),
    inference(resolution,[],[f291,f82])).

fof(f291,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) )
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f290])).

fof(f292,plain,(
    spl2_44 ),
    inference(avatar_split_clause,[],[f61,f290])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f237,plain,
    ( spl2_34
    | ~ spl2_2
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f229,f226,f72,f235])).

fof(f226,plain,
    ( spl2_32
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_2
    | ~ spl2_32 ),
    inference(resolution,[],[f227,f74])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = X1 )
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f226])).

fof(f228,plain,(
    spl2_32 ),
    inference(avatar_split_clause,[],[f50,f226])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f195,plain,
    ( spl2_26
    | ~ spl2_2
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f191,f188,f72,f193])).

fof(f188,plain,
    ( spl2_25
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_2
    | ~ spl2_25 ),
    inference(resolution,[],[f189,f74])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f188])).

fof(f190,plain,(
    spl2_25 ),
    inference(avatar_split_clause,[],[f57,f188])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f181,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f56,f179])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f163,plain,
    ( spl2_19
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f151,f147,f130,f160])).

fof(f130,plain,
    ( spl2_14
  <=> ! [X1,X0] : k4_subset_1(X0,k4_xboole_0(X0,X1),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f147,plain,
    ( spl2_17
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f151,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(superposition,[],[f131,f149])).

fof(f149,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f147])).

fof(f131,plain,
    ( ! [X0,X1] : k4_subset_1(X0,k4_xboole_0(X0,X1),X0) = X0
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f130])).

fof(f157,plain,
    ( spl2_18
    | ~ spl2_6
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f152,f147,f90,f154])).

fof(f90,plain,
    ( spl2_6
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f152,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_6
    | ~ spl2_17 ),
    inference(superposition,[],[f91,f149])).

fof(f91,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f150,plain,
    ( spl2_17
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f144,f141,f123,f147])).

fof(f141,plain,
    ( spl2_16
  <=> ! [X5] : k7_subset_1(u1_struct_0(sK0),sK1,X5) = k4_xboole_0(sK1,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f144,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(superposition,[],[f142,f125])).

fof(f125,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f142,plain,
    ( ! [X5] : k7_subset_1(u1_struct_0(sK0),sK1,X5) = k4_xboole_0(sK1,X5)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl2_16
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f139,f134,f85,f141])).

fof(f134,plain,
    ( spl2_15
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f139,plain,
    ( ! [X5] : k7_subset_1(u1_struct_0(sK0),sK1,X5) = k4_xboole_0(sK1,X5)
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(resolution,[],[f135,f87])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f59,f134])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f132,plain,
    ( spl2_14
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f117,f114,f90,f130])).

fof(f114,plain,
    ( spl2_11
  <=> ! [X1,X2] :
        ( k4_subset_1(X1,X2,X1) = X1
        | ~ r1_tarski(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f117,plain,
    ( ! [X0,X1] : k4_subset_1(X0,k4_xboole_0(X0,X1),X0) = X0
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(resolution,[],[f115,f91])).

fof(f115,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X2,X1)
        | k4_subset_1(X1,X2,X1) = X1 )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f128,plain,
    ( ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f127,f123,f119])).

fof(f127,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f45,f125])).

fof(f45,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f126,plain,
    ( spl2_12
    | spl2_13 ),
    inference(avatar_split_clause,[],[f44,f123,f119])).

fof(f44,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f116,plain,
    ( spl2_11
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f102,f98,f94,f114])).

fof(f98,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k4_subset_1(X0,X1,X0) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f102,plain,
    ( ! [X2,X1] :
        ( k4_subset_1(X1,X2,X1) = X1
        | ~ r1_tarski(X2,X1) )
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(resolution,[],[f99,f95])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k4_subset_1(X0,X1,X0) = X0 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f65,f98])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,X0) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f55,f46])).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(f96,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f58,f94])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f92,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f52,f90])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f88,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f43,f85])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f64,f81])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f47,f46])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f75,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f42,f72])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f41,f67])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:07:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.41  % (32413)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (32402)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (32409)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (32404)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (32403)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (32406)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (32419)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (32409)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f653,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f70,f75,f83,f88,f92,f96,f100,f116,f126,f128,f132,f136,f143,f150,f157,f163,f181,f190,f195,f228,f237,f292,f331,f345,f353,f358,f367,f415,f464,f498,f523,f539,f552,f570,f596,f603,f636,f652])).
% 0.20/0.48  fof(f652,plain,(
% 0.20/0.48    ~spl2_1 | ~spl2_2 | ~spl2_5 | spl2_12 | ~spl2_23 | ~spl2_56),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f651])).
% 0.20/0.48  fof(f651,plain,(
% 0.20/0.48    $false | (~spl2_1 | ~spl2_2 | ~spl2_5 | spl2_12 | ~spl2_23 | ~spl2_56)),
% 0.20/0.48    inference(subsumption_resolution,[],[f650,f69])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    v2_pre_topc(sK0) | ~spl2_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    spl2_1 <=> v2_pre_topc(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.48  fof(f650,plain,(
% 0.20/0.48    ~v2_pre_topc(sK0) | (~spl2_2 | ~spl2_5 | spl2_12 | ~spl2_23 | ~spl2_56)),
% 0.20/0.48    inference(subsumption_resolution,[],[f649,f74])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    l1_pre_topc(sK0) | ~spl2_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    spl2_2 <=> l1_pre_topc(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.48  fof(f649,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl2_5 | spl2_12 | ~spl2_23 | ~spl2_56)),
% 0.20/0.48    inference(subsumption_resolution,[],[f648,f87])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f85])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    spl2_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.48  fof(f648,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl2_12 | ~spl2_23 | ~spl2_56)),
% 0.20/0.48    inference(subsumption_resolution,[],[f640,f120])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ~v4_pre_topc(sK1,sK0) | spl2_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f119])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    spl2_12 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.48  fof(f640,plain,(
% 0.20/0.48    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl2_23 | ~spl2_56)),
% 0.20/0.48    inference(superposition,[],[f180,f366])).
% 0.20/0.48  fof(f366,plain,(
% 0.20/0.48    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_56),
% 0.20/0.48    inference(avatar_component_clause,[],[f364])).
% 0.20/0.48  fof(f364,plain,(
% 0.20/0.48    spl2_56 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 0.20/0.48  fof(f180,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl2_23),
% 0.20/0.48    inference(avatar_component_clause,[],[f179])).
% 0.20/0.48  fof(f179,plain,(
% 0.20/0.48    spl2_23 <=> ! [X1,X0] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.20/0.48  fof(f636,plain,(
% 0.20/0.48    spl2_56 | ~spl2_5 | ~spl2_18 | ~spl2_55 | ~spl2_73 | ~spl2_87 | ~spl2_91),
% 0.20/0.48    inference(avatar_split_clause,[],[f628,f568,f550,f462,f355,f154,f85,f364])).
% 0.20/0.48  fof(f154,plain,(
% 0.20/0.48    spl2_18 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.48  fof(f355,plain,(
% 0.20/0.48    spl2_55 <=> sK1 = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 0.20/0.48  fof(f462,plain,(
% 0.20/0.48    spl2_73 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).
% 0.20/0.48  fof(f550,plain,(
% 0.20/0.48    spl2_87 <=> ! [X1,X2] : (k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X1,X1,X2) | ~r1_tarski(X2,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).
% 0.20/0.48  fof(f568,plain,(
% 0.20/0.48    spl2_91 <=> ! [X1] : (k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X1)) = k3_tarski(k1_enumset1(sK1,sK1,k2_tops_1(sK0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_91])])).
% 0.20/0.48  fof(f628,plain,(
% 0.20/0.48    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_5 | ~spl2_18 | ~spl2_55 | ~spl2_73 | ~spl2_87 | ~spl2_91)),
% 0.20/0.48    inference(forward_demodulation,[],[f627,f357])).
% 0.20/0.48  fof(f357,plain,(
% 0.20/0.48    sK1 = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | ~spl2_55),
% 0.20/0.48    inference(avatar_component_clause,[],[f355])).
% 0.20/0.48  fof(f627,plain,(
% 0.20/0.48    k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) | (~spl2_5 | ~spl2_18 | ~spl2_73 | ~spl2_87 | ~spl2_91)),
% 0.20/0.48    inference(forward_demodulation,[],[f621,f620])).
% 0.20/0.48  fof(f620,plain,(
% 0.20/0.48    k2_pre_topc(sK0,sK1) = k3_tarski(k1_enumset1(sK1,sK1,k2_tops_1(sK0,sK1))) | (~spl2_5 | ~spl2_73 | ~spl2_91)),
% 0.20/0.48    inference(forward_demodulation,[],[f573,f467])).
% 0.20/0.48  fof(f467,plain,(
% 0.20/0.48    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_5 | ~spl2_73)),
% 0.20/0.48    inference(resolution,[],[f463,f87])).
% 0.20/0.48  fof(f463,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_73),
% 0.20/0.48    inference(avatar_component_clause,[],[f462])).
% 0.20/0.48  fof(f573,plain,(
% 0.20/0.48    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k2_tops_1(sK0,sK1))) | (~spl2_5 | ~spl2_91)),
% 0.20/0.48    inference(resolution,[],[f569,f87])).
% 0.20/0.48  fof(f569,plain,(
% 0.20/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X1)) = k3_tarski(k1_enumset1(sK1,sK1,k2_tops_1(sK0,X1)))) ) | ~spl2_91),
% 0.20/0.48    inference(avatar_component_clause,[],[f568])).
% 0.20/0.48  fof(f621,plain,(
% 0.20/0.48    k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k2_tops_1(sK0,sK1))) | (~spl2_18 | ~spl2_87)),
% 0.20/0.48    inference(resolution,[],[f156,f551])).
% 0.20/0.48  fof(f551,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X1,X1,X2)) ) | ~spl2_87),
% 0.20/0.48    inference(avatar_component_clause,[],[f550])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f154])).
% 0.20/0.48  fof(f603,plain,(
% 0.20/0.48    ~spl2_5 | spl2_13 | ~spl2_56 | ~spl2_95),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f602])).
% 0.20/0.48  fof(f602,plain,(
% 0.20/0.48    $false | (~spl2_5 | spl2_13 | ~spl2_56 | ~spl2_95)),
% 0.20/0.48    inference(subsumption_resolution,[],[f601,f124])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f123])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    spl2_13 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.48  fof(f601,plain,(
% 0.20/0.48    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_5 | ~spl2_56 | ~spl2_95)),
% 0.20/0.48    inference(forward_demodulation,[],[f599,f366])).
% 0.20/0.48  fof(f599,plain,(
% 0.20/0.48    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_5 | ~spl2_95)),
% 0.20/0.48    inference(resolution,[],[f595,f87])).
% 0.20/0.48  fof(f595,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | ~spl2_95),
% 0.20/0.48    inference(avatar_component_clause,[],[f594])).
% 0.20/0.48  fof(f594,plain,(
% 0.20/0.48    spl2_95 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).
% 0.20/0.48  fof(f596,plain,(
% 0.20/0.48    spl2_95 | ~spl2_2 | ~spl2_84),
% 0.20/0.48    inference(avatar_split_clause,[],[f592,f537,f72,f594])).
% 0.20/0.48  fof(f537,plain,(
% 0.20/0.48    spl2_84 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_84])])).
% 0.20/0.48  fof(f592,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_84)),
% 0.20/0.48    inference(resolution,[],[f538,f74])).
% 0.20/0.48  fof(f538,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) ) | ~spl2_84),
% 0.20/0.48    inference(avatar_component_clause,[],[f537])).
% 0.20/0.48  fof(f570,plain,(
% 0.20/0.48    spl2_91 | ~spl2_26 | ~spl2_78),
% 0.20/0.48    inference(avatar_split_clause,[],[f502,f496,f193,f568])).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    spl2_26 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.20/0.48  fof(f496,plain,(
% 0.20/0.48    spl2_78 <=> ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X5) = k3_tarski(k1_enumset1(sK1,sK1,X5)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).
% 0.20/0.48  fof(f502,plain,(
% 0.20/0.48    ( ! [X1] : (k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X1)) = k3_tarski(k1_enumset1(sK1,sK1,k2_tops_1(sK0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_26 | ~spl2_78)),
% 0.20/0.48    inference(resolution,[],[f497,f194])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_26),
% 0.20/0.48    inference(avatar_component_clause,[],[f193])).
% 0.20/0.48  fof(f497,plain,(
% 0.20/0.48    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X5) = k3_tarski(k1_enumset1(sK1,sK1,X5))) ) | ~spl2_78),
% 0.20/0.48    inference(avatar_component_clause,[],[f496])).
% 0.20/0.48  fof(f552,plain,(
% 0.20/0.48    spl2_87 | ~spl2_7 | ~spl2_82),
% 0.20/0.48    inference(avatar_split_clause,[],[f525,f521,f94,f550])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    spl2_7 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.48  fof(f521,plain,(
% 0.20/0.48    spl2_82 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k4_subset_1(X1,X1,X0) = k3_tarski(k1_enumset1(X1,X1,X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).
% 0.20/0.48  fof(f525,plain,(
% 0.20/0.48    ( ! [X2,X1] : (k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X1,X1,X2) | ~r1_tarski(X2,X1)) ) | (~spl2_7 | ~spl2_82)),
% 0.20/0.48    inference(resolution,[],[f522,f95])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f94])).
% 0.20/0.48  fof(f522,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k4_subset_1(X1,X1,X0) = k3_tarski(k1_enumset1(X1,X1,X0))) ) | ~spl2_82),
% 0.20/0.48    inference(avatar_component_clause,[],[f521])).
% 0.20/0.48  fof(f539,plain,(
% 0.20/0.48    spl2_84),
% 0.20/0.48    inference(avatar_split_clause,[],[f49,f537])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.20/0.48  fof(f523,plain,(
% 0.20/0.48    spl2_82 | ~spl2_4 | ~spl2_64),
% 0.20/0.48    inference(avatar_split_clause,[],[f471,f413,f81,f521])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    spl2_4 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.48  fof(f413,plain,(
% 0.20/0.48    spl2_64 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).
% 0.20/0.48  fof(f471,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k4_subset_1(X1,X1,X0) = k3_tarski(k1_enumset1(X1,X1,X0))) ) | (~spl2_4 | ~spl2_64)),
% 0.20/0.48    inference(resolution,[],[f414,f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl2_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f81])).
% 0.20/0.48  fof(f414,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))) ) | ~spl2_64),
% 0.20/0.48    inference(avatar_component_clause,[],[f413])).
% 0.20/0.48  fof(f498,plain,(
% 0.20/0.48    spl2_78 | ~spl2_5 | ~spl2_64),
% 0.20/0.48    inference(avatar_split_clause,[],[f473,f413,f85,f496])).
% 0.20/0.48  fof(f473,plain,(
% 0.20/0.48    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X5) = k3_tarski(k1_enumset1(sK1,sK1,X5))) ) | (~spl2_5 | ~spl2_64)),
% 0.20/0.48    inference(resolution,[],[f414,f87])).
% 0.20/0.48  fof(f464,plain,(
% 0.20/0.48    spl2_73 | ~spl2_2 | ~spl2_54),
% 0.20/0.48    inference(avatar_split_clause,[],[f460,f351,f72,f462])).
% 0.20/0.48  fof(f351,plain,(
% 0.20/0.48    spl2_54 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 0.20/0.48  fof(f460,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_54)),
% 0.20/0.48    inference(resolution,[],[f352,f74])).
% 0.20/0.48  fof(f352,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) ) | ~spl2_54),
% 0.20/0.48    inference(avatar_component_clause,[],[f351])).
% 0.20/0.48  fof(f415,plain,(
% 0.20/0.48    spl2_64),
% 0.20/0.48    inference(avatar_split_clause,[],[f63,f413])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f60,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f53,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(flattening,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.48  fof(f367,plain,(
% 0.20/0.48    spl2_56 | ~spl2_5 | ~spl2_12 | ~spl2_34),
% 0.20/0.48    inference(avatar_split_clause,[],[f362,f235,f119,f85,f364])).
% 0.20/0.48  fof(f235,plain,(
% 0.20/0.48    spl2_34 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.20/0.48  fof(f362,plain,(
% 0.20/0.48    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_5 | ~spl2_12 | ~spl2_34)),
% 0.20/0.48    inference(subsumption_resolution,[],[f361,f87])).
% 0.20/0.48  fof(f361,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | (~spl2_12 | ~spl2_34)),
% 0.20/0.48    inference(resolution,[],[f121,f236])).
% 0.20/0.48  fof(f236,plain,(
% 0.20/0.48    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl2_34),
% 0.20/0.48    inference(avatar_component_clause,[],[f235])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    v4_pre_topc(sK1,sK0) | ~spl2_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f119])).
% 0.20/0.48  fof(f358,plain,(
% 0.20/0.48    spl2_55 | ~spl2_18 | ~spl2_19 | ~spl2_53),
% 0.20/0.48    inference(avatar_split_clause,[],[f349,f343,f160,f154,f355])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    spl2_19 <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.48  fof(f343,plain,(
% 0.20/0.48    spl2_53 <=> ! [X1,X2] : (k4_subset_1(X1,X2,X1) = k4_subset_1(X1,X1,X2) | ~r1_tarski(X2,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 0.20/0.48  fof(f349,plain,(
% 0.20/0.48    sK1 = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | (~spl2_18 | ~spl2_19 | ~spl2_53)),
% 0.20/0.48    inference(forward_demodulation,[],[f347,f162])).
% 0.20/0.48  fof(f162,plain,(
% 0.20/0.48    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) | ~spl2_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f160])).
% 0.20/0.48  fof(f347,plain,(
% 0.20/0.48    k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | (~spl2_18 | ~spl2_53)),
% 0.20/0.48    inference(resolution,[],[f344,f156])).
% 0.20/0.48  fof(f344,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k4_subset_1(X1,X2,X1) = k4_subset_1(X1,X1,X2)) ) | ~spl2_53),
% 0.20/0.48    inference(avatar_component_clause,[],[f343])).
% 0.20/0.48  fof(f353,plain,(
% 0.20/0.48    spl2_54),
% 0.20/0.48    inference(avatar_split_clause,[],[f48,f351])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.20/0.48  fof(f345,plain,(
% 0.20/0.48    spl2_53 | ~spl2_7 | ~spl2_51),
% 0.20/0.48    inference(avatar_split_clause,[],[f333,f329,f94,f343])).
% 0.20/0.48  fof(f329,plain,(
% 0.20/0.48    spl2_51 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k4_subset_1(X1,X1,X0) = k4_subset_1(X1,X0,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 0.20/0.48  fof(f333,plain,(
% 0.20/0.48    ( ! [X2,X1] : (k4_subset_1(X1,X2,X1) = k4_subset_1(X1,X1,X2) | ~r1_tarski(X2,X1)) ) | (~spl2_7 | ~spl2_51)),
% 0.20/0.48    inference(resolution,[],[f330,f95])).
% 0.20/0.48  fof(f330,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k4_subset_1(X1,X1,X0) = k4_subset_1(X1,X0,X1)) ) | ~spl2_51),
% 0.20/0.48    inference(avatar_component_clause,[],[f329])).
% 0.20/0.48  fof(f331,plain,(
% 0.20/0.48    spl2_51 | ~spl2_4 | ~spl2_44),
% 0.20/0.48    inference(avatar_split_clause,[],[f324,f290,f81,f329])).
% 0.20/0.48  fof(f290,plain,(
% 0.20/0.48    spl2_44 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.20/0.48  fof(f324,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k4_subset_1(X1,X1,X0) = k4_subset_1(X1,X0,X1)) ) | (~spl2_4 | ~spl2_44)),
% 0.20/0.48    inference(resolution,[],[f291,f82])).
% 0.20/0.48  fof(f291,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)) ) | ~spl2_44),
% 0.20/0.48    inference(avatar_component_clause,[],[f290])).
% 0.20/0.48  fof(f292,plain,(
% 0.20/0.48    spl2_44),
% 0.20/0.48    inference(avatar_split_clause,[],[f61,f290])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(flattening,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 0.20/0.48  fof(f237,plain,(
% 0.20/0.48    spl2_34 | ~spl2_2 | ~spl2_32),
% 0.20/0.48    inference(avatar_split_clause,[],[f229,f226,f72,f235])).
% 0.20/0.48  fof(f226,plain,(
% 0.20/0.48    spl2_32 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.20/0.48  fof(f229,plain,(
% 0.20/0.48    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | (~spl2_2 | ~spl2_32)),
% 0.20/0.48    inference(resolution,[],[f227,f74])).
% 0.20/0.48  fof(f227,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) ) | ~spl2_32),
% 0.20/0.48    inference(avatar_component_clause,[],[f226])).
% 0.20/0.48  fof(f228,plain,(
% 0.20/0.48    spl2_32),
% 0.20/0.48    inference(avatar_split_clause,[],[f50,f226])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.48  fof(f195,plain,(
% 0.20/0.48    spl2_26 | ~spl2_2 | ~spl2_25),
% 0.20/0.48    inference(avatar_split_clause,[],[f191,f188,f72,f193])).
% 0.20/0.48  fof(f188,plain,(
% 0.20/0.48    spl2_25 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.20/0.48  fof(f191,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_2 | ~spl2_25)),
% 0.20/0.48    inference(resolution,[],[f189,f74])).
% 0.20/0.48  fof(f189,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl2_25),
% 0.20/0.48    inference(avatar_component_clause,[],[f188])).
% 0.20/0.48  fof(f190,plain,(
% 0.20/0.48    spl2_25),
% 0.20/0.48    inference(avatar_split_clause,[],[f57,f188])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    spl2_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f56,f179])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.20/0.48  fof(f163,plain,(
% 0.20/0.48    spl2_19 | ~spl2_14 | ~spl2_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f151,f147,f130,f160])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    spl2_14 <=> ! [X1,X0] : k4_subset_1(X0,k4_xboole_0(X0,X1),X0) = X0),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    spl2_17 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.48  fof(f151,plain,(
% 0.20/0.48    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) | (~spl2_14 | ~spl2_17)),
% 0.20/0.48    inference(superposition,[],[f131,f149])).
% 0.20/0.48  fof(f149,plain,(
% 0.20/0.48    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f147])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_subset_1(X0,k4_xboole_0(X0,X1),X0) = X0) ) | ~spl2_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f130])).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    spl2_18 | ~spl2_6 | ~spl2_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f152,f147,f90,f154])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    spl2_6 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_6 | ~spl2_17)),
% 0.20/0.48    inference(superposition,[],[f91,f149])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f90])).
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    spl2_17 | ~spl2_13 | ~spl2_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f144,f141,f123,f147])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    spl2_16 <=> ! [X5] : k7_subset_1(u1_struct_0(sK0),sK1,X5) = k4_xboole_0(sK1,X5)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_13 | ~spl2_16)),
% 0.20/0.48    inference(superposition,[],[f142,f125])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f123])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    ( ! [X5] : (k7_subset_1(u1_struct_0(sK0),sK1,X5) = k4_xboole_0(sK1,X5)) ) | ~spl2_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f141])).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    spl2_16 | ~spl2_5 | ~spl2_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f139,f134,f85,f141])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    spl2_15 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    ( ! [X5] : (k7_subset_1(u1_struct_0(sK0),sK1,X5) = k4_xboole_0(sK1,X5)) ) | (~spl2_5 | ~spl2_15)),
% 0.20/0.48    inference(resolution,[],[f135,f87])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) ) | ~spl2_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f134])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    spl2_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f59,f134])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    spl2_14 | ~spl2_6 | ~spl2_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f117,f114,f90,f130])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    spl2_11 <=> ! [X1,X2] : (k4_subset_1(X1,X2,X1) = X1 | ~r1_tarski(X2,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_subset_1(X0,k4_xboole_0(X0,X1),X0) = X0) ) | (~spl2_6 | ~spl2_11)),
% 0.20/0.48    inference(resolution,[],[f115,f91])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k4_subset_1(X1,X2,X1) = X1) ) | ~spl2_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f114])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ~spl2_12 | ~spl2_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f127,f123,f119])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    ~v4_pre_topc(sK1,sK0) | ~spl2_13),
% 0.20/0.48    inference(subsumption_resolution,[],[f45,f125])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f16])).
% 0.20/0.48  fof(f16,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    spl2_12 | spl2_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f44,f123,f119])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f40])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    spl2_11 | ~spl2_7 | ~spl2_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f102,f98,f94,f114])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    spl2_8 <=> ! [X1,X0] : (k4_subset_1(X0,X1,X0) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    ( ! [X2,X1] : (k4_subset_1(X1,X2,X1) = X1 | ~r1_tarski(X2,X1)) ) | (~spl2_7 | ~spl2_8)),
% 0.20/0.48    inference(resolution,[],[f99,f95])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X0) = X0) ) | ~spl2_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f98])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    spl2_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f65,f98])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_subset_1(X0,X1,X0) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f55,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    spl2_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f58,f94])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.48    inference(unused_predicate_definition_removal,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    spl2_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f52,f90])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    spl2_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f43,f85])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f40])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl2_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f64,f81])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f47,f46])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f42,f72])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f40])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl2_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f41,f67])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f40])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (32409)------------------------------
% 0.20/0.48  % (32409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (32409)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (32409)Memory used [KB]: 6652
% 0.20/0.48  % (32409)Time elapsed: 0.078 s
% 0.20/0.48  % (32409)------------------------------
% 0.20/0.48  % (32409)------------------------------
% 0.20/0.48  % (32410)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (32401)Success in time 0.132 s
%------------------------------------------------------------------------------
