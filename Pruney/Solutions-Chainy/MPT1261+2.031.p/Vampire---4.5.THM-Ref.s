%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:52 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 272 expanded)
%              Number of leaves         :   39 ( 115 expanded)
%              Depth                    :    9
%              Number of atoms          :  357 ( 797 expanded)
%              Number of equality atoms :   96 ( 214 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4092,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f114,f119,f124,f129,f336,f351,f478,f509,f546,f650,f887,f3488,f3499,f3501,f3564,f3565,f3570,f4069,f4091])).

fof(f4091,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) != k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | k6_subset_1(sK1,k1_tops_1(sK0,sK1)) != k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4069,plain,
    ( spl2_275
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f4011,f883,f4066])).

fof(f4066,plain,
    ( spl2_275
  <=> k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_275])])).

fof(f883,plain,
    ( spl2_76
  <=> k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f4011,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_76 ),
    inference(superposition,[],[f183,f885])).

fof(f885,plain,
    ( k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f883])).

fof(f183,plain,(
    ! [X0,X1] : k3_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f72,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f81,f74])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f72,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f3570,plain,
    ( k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | sK1 != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3565,plain,
    ( spl2_216
    | ~ spl2_212 ),
    inference(avatar_split_clause,[],[f3531,f3440,f3459])).

fof(f3459,plain,
    ( spl2_216
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_216])])).

fof(f3440,plain,
    ( spl2_212
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_212])])).

fof(f3531,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_212 ),
    inference(resolution,[],[f3442,f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f82,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f3442,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_212 ),
    inference(avatar_component_clause,[],[f3440])).

fof(f3564,plain,
    ( spl2_218
    | ~ spl2_212 ),
    inference(avatar_split_clause,[],[f3530,f3440,f3469])).

fof(f3469,plain,
    ( spl2_218
  <=> k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_218])])).

fof(f3530,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_212 ),
    inference(resolution,[],[f3442,f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(resolution,[],[f99,f88])).

fof(f3501,plain,
    ( ~ spl2_56
    | spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f3500,f116,f110,f646])).

fof(f646,plain,
    ( spl2_56
  <=> k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f110,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f116,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f3500,plain,
    ( k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f112,f258])).

fof(f258,plain,
    ( ! [X0] : k6_subset_1(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f118,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) ),
    inference(definition_unfolding,[],[f89,f74])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f118,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f112,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f3499,plain,
    ( spl2_212
    | ~ spl2_3
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f3496,f121,f106,f116,f3440])).

fof(f106,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f121,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f3496,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f107,f352])).

fof(f352,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_tops_1(sK0,X0),X0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f70,f123])).

fof(f123,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f107,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f3488,plain,
    ( spl2_221
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f3424,f646,f3485])).

fof(f3485,plain,
    ( spl2_221
  <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_221])])).

fof(f3424,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_56 ),
    inference(superposition,[],[f257,f648])).

fof(f648,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f646])).

fof(f257,plain,(
    ! [X4,X5] : k3_tarski(k2_tarski(X4,k6_subset_1(X4,X5))) = X4 ),
    inference(forward_demodulation,[],[f255,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f255,plain,(
    ! [X4,X5] : k3_tarski(k2_tarski(k6_subset_1(X4,X5),X4)) = X4 ),
    inference(superposition,[],[f97,f176])).

fof(f176,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(forward_demodulation,[],[f98,f73])).

fof(f98,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f79,f76,f75,f74])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f97,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f78,f76,f76,f76])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f887,plain,
    ( spl2_76
    | ~ spl2_3
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f881,f475,f116,f883])).

fof(f475,plain,
    ( spl2_35
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f881,plain,
    ( k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_35 ),
    inference(superposition,[],[f258,f477])).

fof(f477,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f475])).

fof(f650,plain,
    ( spl2_56
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f644,f116,f110,f646])).

fof(f644,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f111,f258])).

fof(f111,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f546,plain,
    ( spl2_39
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f529,f348,f116,f543])).

fof(f543,plain,
    ( spl2_39
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f348,plain,
    ( spl2_20
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f529,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(unit_resulting_resolution,[],[f118,f350,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f93,f76])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f350,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f348])).

fof(f509,plain,
    ( spl2_37
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f495,f121,f116,f506])).

fof(f506,plain,
    ( spl2_37
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f495,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f123,f118,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f478,plain,
    ( spl2_35
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f464,f121,f116,f475])).

fof(f464,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f123,f118,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f351,plain,
    ( spl2_20
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f337,f121,f116,f348])).

fof(f337,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f123,f118,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f336,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f323,f126,f121,f116,f333])).

fof(f333,plain,
    ( spl2_18
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f126,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f323,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f128,f123,f118,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f128,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f129,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f60,f126])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f55,f57,f56])).

fof(f56,plain,
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

fof(f57,plain,
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

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f124,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f61,f121])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f119,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f62,f116])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f114,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f63,f110,f106])).

fof(f63,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f113,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f64,f110,f106])).

fof(f64,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:44:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (14882)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.46  % (14874)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (14879)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (14875)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (14886)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (14887)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (14889)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (14877)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (14876)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (14881)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (14885)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (14883)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.52  % (14892)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.52  % (14878)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (14891)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.53  % (14880)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (14884)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.53  % (14890)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 2.18/0.64  % (14880)Refutation found. Thanks to Tanya!
% 2.18/0.64  % SZS status Theorem for theBenchmark
% 2.18/0.64  % SZS output start Proof for theBenchmark
% 2.18/0.64  fof(f4092,plain,(
% 2.18/0.64    $false),
% 2.18/0.64    inference(avatar_sat_refutation,[],[f113,f114,f119,f124,f129,f336,f351,f478,f509,f546,f650,f887,f3488,f3499,f3501,f3564,f3565,f3570,f4069,f4091])).
% 2.18/0.64  fof(f4091,plain,(
% 2.18/0.64    k6_subset_1(sK1,k2_tops_1(sK0,sK1)) != k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | k1_tops_1(sK0,sK1) != k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | k6_subset_1(sK1,k1_tops_1(sK0,sK1)) != k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 2.18/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.18/0.64  fof(f4069,plain,(
% 2.18/0.64    spl2_275 | ~spl2_76),
% 2.18/0.64    inference(avatar_split_clause,[],[f4011,f883,f4066])).
% 2.18/0.64  fof(f4066,plain,(
% 2.18/0.64    spl2_275 <=> k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_275])])).
% 2.18/0.64  fof(f883,plain,(
% 2.18/0.64    spl2_76 <=> k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 2.18/0.64  fof(f4011,plain,(
% 2.18/0.64    k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_76),
% 2.18/0.64    inference(superposition,[],[f183,f885])).
% 2.18/0.64  fof(f885,plain,(
% 2.18/0.64    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_76),
% 2.18/0.64    inference(avatar_component_clause,[],[f883])).
% 2.18/0.64  fof(f183,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k3_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 2.18/0.64    inference(unit_resulting_resolution,[],[f72,f99])).
% 2.18/0.64  fof(f99,plain,(
% 2.18/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.18/0.64    inference(definition_unfolding,[],[f81,f74])).
% 2.18/0.64  fof(f74,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.18/0.64    inference(cnf_transformation,[],[f18])).
% 2.18/0.64  fof(f18,axiom,(
% 2.18/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.18/0.64  fof(f81,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f39])).
% 2.18/0.64  fof(f39,plain,(
% 2.18/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.64    inference(ennf_transformation,[],[f13])).
% 2.18/0.64  fof(f13,axiom,(
% 2.18/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.18/0.64  fof(f72,plain,(
% 2.18/0.64    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f15])).
% 2.18/0.64  fof(f15,axiom,(
% 2.18/0.64    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 2.18/0.64  fof(f3570,plain,(
% 2.18/0.64    k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | sK1 != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0) | ~v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 2.18/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.18/0.64  fof(f3565,plain,(
% 2.18/0.64    spl2_216 | ~spl2_212),
% 2.18/0.64    inference(avatar_split_clause,[],[f3531,f3440,f3459])).
% 2.18/0.64  fof(f3459,plain,(
% 2.18/0.64    spl2_216 <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_216])])).
% 2.18/0.64  fof(f3440,plain,(
% 2.18/0.64    spl2_212 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_212])])).
% 2.18/0.64  fof(f3531,plain,(
% 2.18/0.64    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_212),
% 2.18/0.64    inference(resolution,[],[f3442,f166])).
% 2.18/0.64  fof(f166,plain,(
% 2.18/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.18/0.64    inference(resolution,[],[f82,f88])).
% 2.18/0.64  fof(f88,plain,(
% 2.18/0.64    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.18/0.64    inference(cnf_transformation,[],[f59])).
% 2.18/0.64  fof(f59,plain,(
% 2.18/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.18/0.64    inference(nnf_transformation,[],[f22])).
% 2.18/0.64  fof(f22,axiom,(
% 2.18/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.18/0.64  fof(f82,plain,(
% 2.18/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.18/0.64    inference(cnf_transformation,[],[f40])).
% 2.18/0.64  fof(f40,plain,(
% 2.18/0.64    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.64    inference(ennf_transformation,[],[f16])).
% 2.18/0.64  fof(f16,axiom,(
% 2.18/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.18/0.64  fof(f3442,plain,(
% 2.18/0.64    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_212),
% 2.18/0.64    inference(avatar_component_clause,[],[f3440])).
% 2.18/0.64  fof(f3564,plain,(
% 2.18/0.64    spl2_218 | ~spl2_212),
% 2.18/0.64    inference(avatar_split_clause,[],[f3530,f3440,f3469])).
% 2.18/0.64  fof(f3469,plain,(
% 2.18/0.64    spl2_218 <=> k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_218])])).
% 2.18/0.64  fof(f3530,plain,(
% 2.18/0.64    k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_212),
% 2.18/0.64    inference(resolution,[],[f3442,f185])).
% 2.18/0.64  fof(f185,plain,(
% 2.18/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.18/0.64    inference(resolution,[],[f99,f88])).
% 2.18/0.64  fof(f3501,plain,(
% 2.18/0.64    ~spl2_56 | spl2_2 | ~spl2_3),
% 2.18/0.64    inference(avatar_split_clause,[],[f3500,f116,f110,f646])).
% 2.18/0.64  fof(f646,plain,(
% 2.18/0.64    spl2_56 <=> k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 2.18/0.64  fof(f110,plain,(
% 2.18/0.64    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.18/0.64  fof(f116,plain,(
% 2.18/0.64    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.18/0.64  fof(f3500,plain,(
% 2.18/0.64    k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (spl2_2 | ~spl2_3)),
% 2.18/0.64    inference(superposition,[],[f112,f258])).
% 2.18/0.64  fof(f258,plain,(
% 2.18/0.64    ( ! [X0] : (k6_subset_1(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 2.18/0.64    inference(unit_resulting_resolution,[],[f118,f101])).
% 2.18/0.64  fof(f101,plain,(
% 2.18/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)) )),
% 2.18/0.64    inference(definition_unfolding,[],[f89,f74])).
% 2.18/0.64  fof(f89,plain,(
% 2.18/0.64    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f47])).
% 2.18/0.64  fof(f47,plain,(
% 2.18/0.64    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.64    inference(ennf_transformation,[],[f19])).
% 2.18/0.64  fof(f19,axiom,(
% 2.18/0.64    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.18/0.64  fof(f118,plain,(
% 2.18/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 2.18/0.64    inference(avatar_component_clause,[],[f116])).
% 2.18/0.64  fof(f112,plain,(
% 2.18/0.64    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 2.18/0.64    inference(avatar_component_clause,[],[f110])).
% 2.18/0.64  fof(f3499,plain,(
% 2.18/0.64    spl2_212 | ~spl2_3 | ~spl2_1 | ~spl2_4),
% 2.18/0.64    inference(avatar_split_clause,[],[f3496,f121,f106,f116,f3440])).
% 2.18/0.64  fof(f106,plain,(
% 2.18/0.64    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.18/0.64  fof(f121,plain,(
% 2.18/0.64    spl2_4 <=> l1_pre_topc(sK0)),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.18/0.64  fof(f3496,plain,(
% 2.18/0.64    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_1 | ~spl2_4)),
% 2.18/0.64    inference(resolution,[],[f107,f352])).
% 2.18/0.64  fof(f352,plain,(
% 2.18/0.64    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_tops_1(sK0,X0),X0)) ) | ~spl2_4),
% 2.18/0.64    inference(resolution,[],[f70,f123])).
% 2.18/0.64  fof(f123,plain,(
% 2.18/0.64    l1_pre_topc(sK0) | ~spl2_4),
% 2.18/0.64    inference(avatar_component_clause,[],[f121])).
% 2.18/0.64  fof(f70,plain,(
% 2.18/0.64    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 2.18/0.64    inference(cnf_transformation,[],[f37])).
% 2.18/0.64  fof(f37,plain,(
% 2.18/0.64    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.64    inference(flattening,[],[f36])).
% 2.18/0.64  fof(f36,plain,(
% 2.18/0.64    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.64    inference(ennf_transformation,[],[f27])).
% 2.18/0.64  fof(f27,axiom,(
% 2.18/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 2.18/0.64  fof(f107,plain,(
% 2.18/0.64    v4_pre_topc(sK1,sK0) | ~spl2_1),
% 2.18/0.64    inference(avatar_component_clause,[],[f106])).
% 2.18/0.64  fof(f3488,plain,(
% 2.18/0.64    spl2_221 | ~spl2_56),
% 2.18/0.64    inference(avatar_split_clause,[],[f3424,f646,f3485])).
% 2.18/0.64  fof(f3485,plain,(
% 2.18/0.64    spl2_221 <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_221])])).
% 2.18/0.64  fof(f3424,plain,(
% 2.18/0.64    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_56),
% 2.18/0.64    inference(superposition,[],[f257,f648])).
% 2.18/0.64  fof(f648,plain,(
% 2.18/0.64    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_56),
% 2.18/0.64    inference(avatar_component_clause,[],[f646])).
% 2.18/0.64  fof(f257,plain,(
% 2.18/0.64    ( ! [X4,X5] : (k3_tarski(k2_tarski(X4,k6_subset_1(X4,X5))) = X4) )),
% 2.18/0.64    inference(forward_demodulation,[],[f255,f73])).
% 2.18/0.64  fof(f73,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.18/0.64    inference(cnf_transformation,[],[f10])).
% 2.18/0.64  fof(f10,axiom,(
% 2.18/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.18/0.64  fof(f255,plain,(
% 2.18/0.64    ( ! [X4,X5] : (k3_tarski(k2_tarski(k6_subset_1(X4,X5),X4)) = X4) )),
% 2.18/0.64    inference(superposition,[],[f97,f176])).
% 2.18/0.64  fof(f176,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k3_tarski(k2_tarski(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 2.18/0.64    inference(forward_demodulation,[],[f98,f73])).
% 2.18/0.64  fof(f98,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) = X0) )),
% 2.18/0.64    inference(definition_unfolding,[],[f79,f76,f75,f74])).
% 2.18/0.64  fof(f75,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f21])).
% 2.18/0.64  fof(f21,axiom,(
% 2.18/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.18/0.64  fof(f76,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f11])).
% 2.18/0.64  fof(f11,axiom,(
% 2.18/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.18/0.64  fof(f79,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.18/0.64    inference(cnf_transformation,[],[f8])).
% 2.18/0.64  fof(f8,axiom,(
% 2.18/0.64    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.18/0.64  fof(f97,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )),
% 2.18/0.64    inference(definition_unfolding,[],[f78,f76,f76,f76])).
% 2.18/0.64  fof(f78,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f9])).
% 2.18/0.64  fof(f9,axiom,(
% 2.18/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 2.18/0.64  fof(f887,plain,(
% 2.18/0.64    spl2_76 | ~spl2_3 | ~spl2_35),
% 2.18/0.64    inference(avatar_split_clause,[],[f881,f475,f116,f883])).
% 2.18/0.64  fof(f475,plain,(
% 2.18/0.64    spl2_35 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 2.18/0.64  fof(f881,plain,(
% 2.18/0.64    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_35)),
% 2.18/0.64    inference(superposition,[],[f258,f477])).
% 2.18/0.64  fof(f477,plain,(
% 2.18/0.64    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_35),
% 2.18/0.64    inference(avatar_component_clause,[],[f475])).
% 2.18/0.64  fof(f650,plain,(
% 2.18/0.64    spl2_56 | ~spl2_2 | ~spl2_3),
% 2.18/0.64    inference(avatar_split_clause,[],[f644,f116,f110,f646])).
% 2.18/0.64  fof(f644,plain,(
% 2.18/0.64    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 2.18/0.64    inference(superposition,[],[f111,f258])).
% 2.18/0.64  fof(f111,plain,(
% 2.18/0.64    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 2.18/0.64    inference(avatar_component_clause,[],[f110])).
% 2.18/0.64  fof(f546,plain,(
% 2.18/0.64    spl2_39 | ~spl2_3 | ~spl2_20),
% 2.18/0.64    inference(avatar_split_clause,[],[f529,f348,f116,f543])).
% 2.18/0.64  fof(f543,plain,(
% 2.18/0.64    spl2_39 <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 2.18/0.64  fof(f348,plain,(
% 2.18/0.64    spl2_20 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 2.18/0.64  fof(f529,plain,(
% 2.18/0.64    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_20)),
% 2.18/0.64    inference(unit_resulting_resolution,[],[f118,f350,f104])).
% 2.18/0.64  fof(f104,plain,(
% 2.18/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))) )),
% 2.18/0.64    inference(definition_unfolding,[],[f93,f76])).
% 2.18/0.64  fof(f93,plain,(
% 2.18/0.64    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f53])).
% 2.18/0.64  fof(f53,plain,(
% 2.18/0.64    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.64    inference(flattening,[],[f52])).
% 2.18/0.64  fof(f52,plain,(
% 2.18/0.64    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.18/0.64    inference(ennf_transformation,[],[f17])).
% 2.18/0.64  fof(f17,axiom,(
% 2.18/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.18/0.64  fof(f350,plain,(
% 2.18/0.64    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_20),
% 2.18/0.64    inference(avatar_component_clause,[],[f348])).
% 2.18/0.64  fof(f509,plain,(
% 2.18/0.64    spl2_37 | ~spl2_3 | ~spl2_4),
% 2.18/0.64    inference(avatar_split_clause,[],[f495,f121,f116,f506])).
% 2.18/0.64  fof(f506,plain,(
% 2.18/0.64    spl2_37 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 2.18/0.64  fof(f495,plain,(
% 2.18/0.64    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 2.18/0.64    inference(unit_resulting_resolution,[],[f123,f118,f69])).
% 2.18/0.64  fof(f69,plain,(
% 2.18/0.64    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f35])).
% 2.18/0.64  fof(f35,plain,(
% 2.18/0.64    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.64    inference(ennf_transformation,[],[f26])).
% 2.18/0.64  fof(f26,axiom,(
% 2.18/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 2.18/0.64  fof(f478,plain,(
% 2.18/0.64    spl2_35 | ~spl2_3 | ~spl2_4),
% 2.18/0.64    inference(avatar_split_clause,[],[f464,f121,f116,f475])).
% 2.18/0.64  fof(f464,plain,(
% 2.18/0.64    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 2.18/0.64    inference(unit_resulting_resolution,[],[f123,f118,f68])).
% 2.18/0.64  fof(f68,plain,(
% 2.18/0.64    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f34])).
% 2.18/0.64  fof(f34,plain,(
% 2.18/0.64    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.64    inference(ennf_transformation,[],[f28])).
% 2.18/0.64  fof(f28,axiom,(
% 2.18/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 2.18/0.64  fof(f351,plain,(
% 2.18/0.64    spl2_20 | ~spl2_3 | ~spl2_4),
% 2.18/0.64    inference(avatar_split_clause,[],[f337,f121,f116,f348])).
% 2.18/0.64  fof(f337,plain,(
% 2.18/0.64    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_4)),
% 2.18/0.64    inference(unit_resulting_resolution,[],[f123,f118,f86])).
% 2.18/0.64  fof(f86,plain,(
% 2.18/0.64    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f46])).
% 2.18/0.64  fof(f46,plain,(
% 2.18/0.64    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.18/0.64    inference(flattening,[],[f45])).
% 2.18/0.64  fof(f45,plain,(
% 2.18/0.64    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.18/0.64    inference(ennf_transformation,[],[f23])).
% 2.18/0.64  fof(f23,axiom,(
% 2.18/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.18/0.64  fof(f336,plain,(
% 2.18/0.64    spl2_18 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 2.18/0.64    inference(avatar_split_clause,[],[f323,f126,f121,f116,f333])).
% 2.18/0.64  fof(f333,plain,(
% 2.18/0.64    spl2_18 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 2.18/0.64  fof(f126,plain,(
% 2.18/0.64    spl2_5 <=> v2_pre_topc(sK0)),
% 2.18/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.18/0.64  fof(f323,plain,(
% 2.18/0.64    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 2.18/0.64    inference(unit_resulting_resolution,[],[f128,f123,f118,f85])).
% 2.18/0.64  fof(f85,plain,(
% 2.18/0.64    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.18/0.64    inference(cnf_transformation,[],[f44])).
% 2.18/0.64  fof(f44,plain,(
% 2.18/0.64    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.18/0.64    inference(flattening,[],[f43])).
% 2.18/0.64  fof(f43,plain,(
% 2.18/0.64    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.18/0.64    inference(ennf_transformation,[],[f24])).
% 2.18/0.64  fof(f24,axiom,(
% 2.18/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 2.18/0.64  fof(f128,plain,(
% 2.18/0.64    v2_pre_topc(sK0) | ~spl2_5),
% 2.18/0.64    inference(avatar_component_clause,[],[f126])).
% 2.18/0.64  fof(f129,plain,(
% 2.18/0.64    spl2_5),
% 2.18/0.64    inference(avatar_split_clause,[],[f60,f126])).
% 2.18/0.64  fof(f60,plain,(
% 2.18/0.64    v2_pre_topc(sK0)),
% 2.18/0.64    inference(cnf_transformation,[],[f58])).
% 2.18/0.64  fof(f58,plain,(
% 2.18/0.64    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.18/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f55,f57,f56])).
% 2.18/0.64  fof(f56,plain,(
% 2.18/0.64    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.18/0.64    introduced(choice_axiom,[])).
% 2.18/0.64  fof(f57,plain,(
% 2.18/0.64    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.18/0.64    introduced(choice_axiom,[])).
% 2.18/0.64  fof(f55,plain,(
% 2.18/0.64    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.18/0.64    inference(flattening,[],[f54])).
% 2.18/0.64  fof(f54,plain,(
% 2.18/0.64    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.18/0.64    inference(nnf_transformation,[],[f32])).
% 2.18/0.64  fof(f32,plain,(
% 2.18/0.64    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.18/0.64    inference(flattening,[],[f31])).
% 2.18/0.64  fof(f31,plain,(
% 2.18/0.64    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.18/0.64    inference(ennf_transformation,[],[f30])).
% 2.18/0.64  fof(f30,negated_conjecture,(
% 2.18/0.64    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.18/0.64    inference(negated_conjecture,[],[f29])).
% 2.18/0.64  fof(f29,conjecture,(
% 2.18/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 2.18/0.64  fof(f124,plain,(
% 2.18/0.64    spl2_4),
% 2.18/0.64    inference(avatar_split_clause,[],[f61,f121])).
% 2.18/0.64  fof(f61,plain,(
% 2.18/0.64    l1_pre_topc(sK0)),
% 2.18/0.64    inference(cnf_transformation,[],[f58])).
% 2.18/0.64  fof(f119,plain,(
% 2.18/0.64    spl2_3),
% 2.18/0.64    inference(avatar_split_clause,[],[f62,f116])).
% 2.18/0.64  fof(f62,plain,(
% 2.18/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.64    inference(cnf_transformation,[],[f58])).
% 2.18/0.64  fof(f114,plain,(
% 2.18/0.64    spl2_1 | spl2_2),
% 2.18/0.64    inference(avatar_split_clause,[],[f63,f110,f106])).
% 2.18/0.64  fof(f63,plain,(
% 2.18/0.64    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.18/0.64    inference(cnf_transformation,[],[f58])).
% 2.18/0.64  fof(f113,plain,(
% 2.18/0.64    ~spl2_1 | ~spl2_2),
% 2.18/0.64    inference(avatar_split_clause,[],[f64,f110,f106])).
% 2.18/0.64  fof(f64,plain,(
% 2.18/0.64    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.18/0.64    inference(cnf_transformation,[],[f58])).
% 2.18/0.64  % SZS output end Proof for theBenchmark
% 2.18/0.64  % (14880)------------------------------
% 2.18/0.64  % (14880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.64  % (14880)Termination reason: Refutation
% 2.18/0.64  
% 2.18/0.64  % (14880)Memory used [KB]: 8827
% 2.18/0.64  % (14880)Time elapsed: 0.227 s
% 2.18/0.64  % (14880)------------------------------
% 2.18/0.64  % (14880)------------------------------
% 2.18/0.65  % (14873)Success in time 0.282 s
%------------------------------------------------------------------------------
