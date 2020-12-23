%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:27 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 187 expanded)
%              Number of leaves         :   32 (  91 expanded)
%              Depth                    :    7
%              Number of atoms          :  297 ( 469 expanded)
%              Number of equality atoms :   78 ( 134 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f379,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f48,f52,f56,f60,f64,f76,f84,f90,f94,f98,f105,f120,f137,f147,f151,f159,f181,f317,f359,f378])).

fof(f378,plain,
    ( spl2_20
    | ~ spl2_22
    | ~ spl2_40 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | spl2_20
    | ~ spl2_22
    | ~ spl2_40 ),
    inference(subsumption_resolution,[],[f146,f371])).

fof(f371,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_22
    | ~ spl2_40 ),
    inference(superposition,[],[f358,f158])).

fof(f158,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl2_22
  <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f358,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl2_40
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f146,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl2_20 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl2_20
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f359,plain,
    ( spl2_40
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f318,f315,f81,f46,f356])).

fof(f46,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f81,plain,
    ( spl2_11
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f315,plain,
    ( spl2_36
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0
        | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f318,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_36 ),
    inference(unit_resulting_resolution,[],[f83,f47,f316])).

fof(f316,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f315])).

fof(f47,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f83,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f317,plain,
    ( spl2_36
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_14
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f191,f179,f96,f54,f50,f315])).

fof(f50,plain,
    ( spl2_4
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f54,plain,
    ( spl2_5
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f96,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f179,plain,
    ( spl2_24
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_14
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f190,f51])).

fof(f51,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_5
    | ~ spl2_14
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f187,f55])).

fof(f55,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k2_relat_1(k6_relat_1(X0))
        | ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_14
    | ~ spl2_24 ),
    inference(superposition,[],[f180,f97])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f96])).

fof(f180,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f179])).

fof(f181,plain,
    ( spl2_24
    | ~ spl2_3
    | ~ spl2_18
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f155,f149,f135,f46,f179])).

fof(f135,plain,
    ( spl2_18
  <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f149,plain,
    ( spl2_21
  <=> ! [X3,X2] :
        ( k2_relat_1(k7_relat_1(X3,X2)) = k9_relat_1(X3,X2)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f155,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_3
    | ~ spl2_18
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f152,f136])).

fof(f136,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f135])).

fof(f152,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(unit_resulting_resolution,[],[f47,f47,f150])).

fof(f150,plain,
    ( ! [X2,X3] :
        ( k2_relat_1(k7_relat_1(X3,X2)) = k9_relat_1(X3,X2)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(k6_relat_1(X2)) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f149])).

fof(f159,plain,
    ( spl2_22
    | ~ spl2_10
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f123,f118,f74,f157])).

fof(f74,plain,
    ( spl2_10
  <=> ! [X1,X0] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f118,plain,
    ( spl2_16
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f123,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_10
    | ~ spl2_16 ),
    inference(superposition,[],[f119,f75])).

fof(f75,plain,
    ( ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f119,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f151,plain,
    ( spl2_21
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f116,f103,f92,f54,f149])).

fof(f92,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f103,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

% (12089)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f116,plain,
    ( ! [X2,X3] :
        ( k2_relat_1(k7_relat_1(X3,X2)) = k9_relat_1(X3,X2)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(k6_relat_1(X2)) )
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f110,f55])).

fof(f110,plain,
    ( ! [X2,X3] :
        ( k9_relat_1(X3,k2_relat_1(k6_relat_1(X2))) = k2_relat_1(k7_relat_1(X3,X2))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(k6_relat_1(X2)) )
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,
    ( ! [X2,X3] :
        ( k9_relat_1(X3,k2_relat_1(k6_relat_1(X2))) = k2_relat_1(k7_relat_1(X3,X2))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(X3) )
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(superposition,[],[f104,f93])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f103])).

fof(f147,plain,
    ( ~ spl2_20
    | spl2_2
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f138,f135,f41,f144])).

fof(f41,plain,
    ( spl2_2
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f138,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl2_2
    | ~ spl2_18 ),
    inference(superposition,[],[f43,f136])).

fof(f43,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f137,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f113,f103,f88,f54,f46,f135])).

fof(f88,plain,
    ( spl2_12
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f113,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f112,f55])).

fof(f112,plain,
    ( ! [X0,X1] : k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f111,f89])).

fof(f89,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f111,plain,
    ( ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f107,f55])).

fof(f107,plain,
    ( ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0)))
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f47,f47,f104])).

fof(f120,plain,
    ( spl2_16
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f85,f74,f58,f118])).

fof(f58,plain,
    ( spl2_6
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f85,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(superposition,[],[f75,f59])).

fof(f59,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f105,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f26,f103])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f98,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f32,f96])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f94,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f31,f92])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f90,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f30,f88])).

fof(f30,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f84,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f77,f62,f36,f81])).

fof(f36,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f62,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f77,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f38,f63])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f38,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f76,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f29,f74])).

fof(f29,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f64,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f33,f62])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

% (12091)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f60,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f56,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f52,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f44,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f22,f41])).

fof(f22,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f39,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f21,f36])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:19:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.46  % (12087)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.48  % (12082)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.48  % (12074)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.48  % (12081)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.48  % (12079)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.48  % (12083)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.49  % (12078)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.49  % (12088)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.49  % (12079)Refutation found. Thanks to Tanya!
% 0.23/0.49  % SZS status Theorem for theBenchmark
% 0.23/0.49  % (12084)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.49  % (12075)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.50  % (12086)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.50  % (12080)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f379,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(avatar_sat_refutation,[],[f39,f44,f48,f52,f56,f60,f64,f76,f84,f90,f94,f98,f105,f120,f137,f147,f151,f159,f181,f317,f359,f378])).
% 0.23/0.50  fof(f378,plain,(
% 0.23/0.50    spl2_20 | ~spl2_22 | ~spl2_40),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f377])).
% 0.23/0.50  fof(f377,plain,(
% 0.23/0.50    $false | (spl2_20 | ~spl2_22 | ~spl2_40)),
% 0.23/0.50    inference(subsumption_resolution,[],[f146,f371])).
% 0.23/0.50  fof(f371,plain,(
% 0.23/0.50    sK1 = k3_xboole_0(sK0,sK1) | (~spl2_22 | ~spl2_40)),
% 0.23/0.50    inference(superposition,[],[f358,f158])).
% 0.23/0.50  fof(f158,plain,(
% 0.23/0.50    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | ~spl2_22),
% 0.23/0.50    inference(avatar_component_clause,[],[f157])).
% 0.23/0.50  fof(f157,plain,(
% 0.23/0.50    spl2_22 <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.23/0.50  fof(f358,plain,(
% 0.23/0.50    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_40),
% 0.23/0.50    inference(avatar_component_clause,[],[f356])).
% 0.23/0.50  fof(f356,plain,(
% 0.23/0.50    spl2_40 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.23/0.50  fof(f146,plain,(
% 0.23/0.50    sK1 != k3_xboole_0(sK0,sK1) | spl2_20),
% 0.23/0.50    inference(avatar_component_clause,[],[f144])).
% 0.23/0.50  fof(f144,plain,(
% 0.23/0.50    spl2_20 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.23/0.50  fof(f359,plain,(
% 0.23/0.50    spl2_40 | ~spl2_3 | ~spl2_11 | ~spl2_36),
% 0.23/0.50    inference(avatar_split_clause,[],[f318,f315,f81,f46,f356])).
% 0.23/0.50  fof(f46,plain,(
% 0.23/0.50    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.23/0.50  fof(f81,plain,(
% 0.23/0.50    spl2_11 <=> r1_tarski(sK1,sK0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.23/0.50  fof(f315,plain,(
% 0.23/0.50    spl2_36 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 | ~v1_relat_1(k6_relat_1(X0)))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.23/0.50  fof(f318,plain,(
% 0.23/0.50    sK1 = k3_xboole_0(sK1,sK0) | (~spl2_3 | ~spl2_11 | ~spl2_36)),
% 0.23/0.50    inference(unit_resulting_resolution,[],[f83,f47,f316])).
% 0.23/0.50  fof(f316,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1) | ~v1_relat_1(k6_relat_1(X0))) ) | ~spl2_36),
% 0.23/0.50    inference(avatar_component_clause,[],[f315])).
% 0.23/0.50  fof(f47,plain,(
% 0.23/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.23/0.50    inference(avatar_component_clause,[],[f46])).
% 0.23/0.50  fof(f83,plain,(
% 0.23/0.50    r1_tarski(sK1,sK0) | ~spl2_11),
% 0.23/0.50    inference(avatar_component_clause,[],[f81])).
% 0.23/0.50  fof(f317,plain,(
% 0.23/0.50    spl2_36 | ~spl2_4 | ~spl2_5 | ~spl2_14 | ~spl2_24),
% 0.23/0.50    inference(avatar_split_clause,[],[f191,f179,f96,f54,f50,f315])).
% 0.23/0.50  fof(f50,plain,(
% 0.23/0.50    spl2_4 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.23/0.50  fof(f54,plain,(
% 0.23/0.50    spl2_5 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.23/0.50  fof(f96,plain,(
% 0.23/0.50    spl2_14 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.23/0.50  fof(f179,plain,(
% 0.23/0.50    spl2_24 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.23/0.50  fof(f191,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_4 | ~spl2_5 | ~spl2_14 | ~spl2_24)),
% 0.23/0.50    inference(forward_demodulation,[],[f190,f51])).
% 0.23/0.50  fof(f51,plain,(
% 0.23/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.23/0.50    inference(avatar_component_clause,[],[f50])).
% 0.23/0.50  fof(f190,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_5 | ~spl2_14 | ~spl2_24)),
% 0.23/0.50    inference(forward_demodulation,[],[f187,f55])).
% 0.23/0.50  fof(f55,plain,(
% 0.23/0.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_5),
% 0.23/0.50    inference(avatar_component_clause,[],[f54])).
% 0.23/0.50  fof(f187,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k2_relat_1(k6_relat_1(X0)) | ~r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_14 | ~spl2_24)),
% 0.23/0.50    inference(superposition,[],[f180,f97])).
% 0.23/0.50  fof(f97,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_14),
% 0.23/0.50    inference(avatar_component_clause,[],[f96])).
% 0.23/0.50  fof(f180,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | ~spl2_24),
% 0.23/0.50    inference(avatar_component_clause,[],[f179])).
% 0.23/0.50  fof(f181,plain,(
% 0.23/0.50    spl2_24 | ~spl2_3 | ~spl2_18 | ~spl2_21),
% 0.23/0.50    inference(avatar_split_clause,[],[f155,f149,f135,f46,f179])).
% 0.23/0.50  fof(f135,plain,(
% 0.23/0.50    spl2_18 <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.23/0.50  fof(f149,plain,(
% 0.23/0.50    spl2_21 <=> ! [X3,X2] : (k2_relat_1(k7_relat_1(X3,X2)) = k9_relat_1(X3,X2) | ~v1_relat_1(X3) | ~v1_relat_1(k6_relat_1(X2)))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.23/0.50  fof(f155,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_3 | ~spl2_18 | ~spl2_21)),
% 0.23/0.50    inference(forward_demodulation,[],[f152,f136])).
% 0.23/0.50  fof(f136,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)) ) | ~spl2_18),
% 0.23/0.50    inference(avatar_component_clause,[],[f135])).
% 0.23/0.50  fof(f152,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_3 | ~spl2_21)),
% 0.23/0.50    inference(unit_resulting_resolution,[],[f47,f47,f150])).
% 0.23/0.50  fof(f150,plain,(
% 0.23/0.50    ( ! [X2,X3] : (k2_relat_1(k7_relat_1(X3,X2)) = k9_relat_1(X3,X2) | ~v1_relat_1(X3) | ~v1_relat_1(k6_relat_1(X2))) ) | ~spl2_21),
% 0.23/0.50    inference(avatar_component_clause,[],[f149])).
% 0.23/0.50  fof(f159,plain,(
% 0.23/0.50    spl2_22 | ~spl2_10 | ~spl2_16),
% 0.23/0.50    inference(avatar_split_clause,[],[f123,f118,f74,f157])).
% 0.23/0.50  fof(f74,plain,(
% 0.23/0.50    spl2_10 <=> ! [X1,X0] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.23/0.50  fof(f118,plain,(
% 0.23/0.50    spl2_16 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.23/0.50  fof(f123,plain,(
% 0.23/0.50    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | (~spl2_10 | ~spl2_16)),
% 0.23/0.50    inference(superposition,[],[f119,f75])).
% 0.23/0.50  fof(f75,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) ) | ~spl2_10),
% 0.23/0.50    inference(avatar_component_clause,[],[f74])).
% 0.23/0.50  fof(f119,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | ~spl2_16),
% 0.23/0.50    inference(avatar_component_clause,[],[f118])).
% 0.23/0.50  fof(f151,plain,(
% 0.23/0.50    spl2_21 | ~spl2_5 | ~spl2_13 | ~spl2_15),
% 0.23/0.50    inference(avatar_split_clause,[],[f116,f103,f92,f54,f149])).
% 0.23/0.50  fof(f92,plain,(
% 0.23/0.50    spl2_13 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.23/0.50  fof(f103,plain,(
% 0.23/0.50    spl2_15 <=> ! [X1,X0] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.23/0.50  % (12089)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.50  fof(f116,plain,(
% 0.23/0.50    ( ! [X2,X3] : (k2_relat_1(k7_relat_1(X3,X2)) = k9_relat_1(X3,X2) | ~v1_relat_1(X3) | ~v1_relat_1(k6_relat_1(X2))) ) | (~spl2_5 | ~spl2_13 | ~spl2_15)),
% 0.23/0.50    inference(forward_demodulation,[],[f110,f55])).
% 0.23/0.50  fof(f110,plain,(
% 0.23/0.50    ( ! [X2,X3] : (k9_relat_1(X3,k2_relat_1(k6_relat_1(X2))) = k2_relat_1(k7_relat_1(X3,X2)) | ~v1_relat_1(X3) | ~v1_relat_1(k6_relat_1(X2))) ) | (~spl2_13 | ~spl2_15)),
% 0.23/0.50    inference(duplicate_literal_removal,[],[f109])).
% 0.23/0.50  fof(f109,plain,(
% 0.23/0.50    ( ! [X2,X3] : (k9_relat_1(X3,k2_relat_1(k6_relat_1(X2))) = k2_relat_1(k7_relat_1(X3,X2)) | ~v1_relat_1(X3) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(X3)) ) | (~spl2_13 | ~spl2_15)),
% 0.23/0.50    inference(superposition,[],[f104,f93])).
% 0.23/0.50  fof(f93,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) ) | ~spl2_13),
% 0.23/0.50    inference(avatar_component_clause,[],[f92])).
% 0.23/0.50  fof(f104,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_15),
% 0.23/0.50    inference(avatar_component_clause,[],[f103])).
% 0.23/0.50  fof(f147,plain,(
% 0.23/0.50    ~spl2_20 | spl2_2 | ~spl2_18),
% 0.23/0.50    inference(avatar_split_clause,[],[f138,f135,f41,f144])).
% 0.23/0.50  fof(f41,plain,(
% 0.23/0.50    spl2_2 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.50  fof(f138,plain,(
% 0.23/0.50    sK1 != k3_xboole_0(sK0,sK1) | (spl2_2 | ~spl2_18)),
% 0.23/0.50    inference(superposition,[],[f43,f136])).
% 0.23/0.50  fof(f43,plain,(
% 0.23/0.50    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_2),
% 0.23/0.50    inference(avatar_component_clause,[],[f41])).
% 0.23/0.50  fof(f137,plain,(
% 0.23/0.50    spl2_18 | ~spl2_3 | ~spl2_5 | ~spl2_12 | ~spl2_15),
% 0.23/0.50    inference(avatar_split_clause,[],[f113,f103,f88,f54,f46,f135])).
% 0.23/0.50  fof(f88,plain,(
% 0.23/0.50    spl2_12 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.23/0.50  fof(f113,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_3 | ~spl2_5 | ~spl2_12 | ~spl2_15)),
% 0.23/0.50    inference(forward_demodulation,[],[f112,f55])).
% 0.23/0.50  fof(f112,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) = k9_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_3 | ~spl2_5 | ~spl2_12 | ~spl2_15)),
% 0.23/0.50    inference(forward_demodulation,[],[f111,f89])).
% 0.23/0.50  fof(f89,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_12),
% 0.23/0.50    inference(avatar_component_clause,[],[f88])).
% 0.23/0.50  fof(f111,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_3 | ~spl2_5 | ~spl2_15)),
% 0.23/0.50    inference(forward_demodulation,[],[f107,f55])).
% 0.23/0.50  fof(f107,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0)))) ) | (~spl2_3 | ~spl2_15)),
% 0.23/0.50    inference(unit_resulting_resolution,[],[f47,f47,f104])).
% 0.23/0.50  fof(f120,plain,(
% 0.23/0.50    spl2_16 | ~spl2_6 | ~spl2_10),
% 0.23/0.50    inference(avatar_split_clause,[],[f85,f74,f58,f118])).
% 0.23/0.50  fof(f58,plain,(
% 0.23/0.50    spl2_6 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.23/0.50  fof(f85,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl2_6 | ~spl2_10)),
% 0.23/0.50    inference(superposition,[],[f75,f59])).
% 0.23/0.50  fof(f59,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_6),
% 0.23/0.50    inference(avatar_component_clause,[],[f58])).
% 0.23/0.50  fof(f105,plain,(
% 0.23/0.50    spl2_15),
% 0.23/0.50    inference(avatar_split_clause,[],[f26,f103])).
% 0.23/0.51  fof(f26,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f14])).
% 0.23/0.51  fof(f14,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f6])).
% 0.23/0.51  fof(f6,axiom,(
% 0.23/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.23/0.51  fof(f98,plain,(
% 0.23/0.51    spl2_14),
% 0.23/0.51    inference(avatar_split_clause,[],[f32,f96])).
% 0.23/0.51  fof(f32,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f17])).
% 0.23/0.51  fof(f17,plain,(
% 0.23/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.23/0.51    inference(flattening,[],[f16])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f9])).
% 0.23/0.51  fof(f9,axiom,(
% 0.23/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.23/0.51  fof(f94,plain,(
% 0.23/0.51    spl2_13),
% 0.23/0.51    inference(avatar_split_clause,[],[f31,f92])).
% 0.23/0.51  fof(f31,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f15])).
% 0.23/0.51  fof(f15,plain,(
% 0.23/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f8])).
% 0.23/0.51  fof(f8,axiom,(
% 0.23/0.51    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.23/0.51  fof(f90,plain,(
% 0.23/0.51    spl2_12),
% 0.23/0.51    inference(avatar_split_clause,[],[f30,f88])).
% 0.23/0.51  fof(f30,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f10])).
% 0.23/0.51  fof(f10,axiom,(
% 0.23/0.51    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.23/0.51  fof(f84,plain,(
% 0.23/0.51    spl2_11 | ~spl2_1 | ~spl2_7),
% 0.23/0.51    inference(avatar_split_clause,[],[f77,f62,f36,f81])).
% 0.23/0.51  fof(f36,plain,(
% 0.23/0.51    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.51  fof(f62,plain,(
% 0.23/0.51    spl2_7 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.23/0.51  fof(f77,plain,(
% 0.23/0.51    r1_tarski(sK1,sK0) | (~spl2_1 | ~spl2_7)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f38,f63])).
% 0.23/0.51  fof(f63,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_7),
% 0.23/0.51    inference(avatar_component_clause,[],[f62])).
% 0.23/0.51  fof(f38,plain,(
% 0.23/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.23/0.51    inference(avatar_component_clause,[],[f36])).
% 0.23/0.51  fof(f76,plain,(
% 0.23/0.51    spl2_10),
% 0.23/0.51    inference(avatar_split_clause,[],[f29,f74])).
% 0.23/0.51  fof(f29,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f3])).
% 0.23/0.51  fof(f3,axiom,(
% 0.23/0.51    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.23/0.51  fof(f64,plain,(
% 0.23/0.51    spl2_7),
% 0.23/0.51    inference(avatar_split_clause,[],[f33,f62])).
% 0.23/0.51  fof(f33,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f20])).
% 0.23/0.51  % (12091)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.23/0.51    inference(nnf_transformation,[],[f4])).
% 0.23/0.51  fof(f4,axiom,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.51  fof(f60,plain,(
% 0.23/0.51    spl2_6),
% 0.23/0.51    inference(avatar_split_clause,[],[f27,f58])).
% 0.23/0.51  fof(f27,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f1])).
% 0.23/0.51  fof(f1,axiom,(
% 0.23/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.23/0.51  fof(f56,plain,(
% 0.23/0.51    spl2_5),
% 0.23/0.51    inference(avatar_split_clause,[],[f25,f54])).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.23/0.51    inference(cnf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,axiom,(
% 0.23/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.23/0.51  fof(f52,plain,(
% 0.23/0.51    spl2_4),
% 0.23/0.51    inference(avatar_split_clause,[],[f24,f50])).
% 0.23/0.51  fof(f24,plain,(
% 0.23/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.23/0.51    inference(cnf_transformation,[],[f7])).
% 0.23/0.51  fof(f48,plain,(
% 0.23/0.51    spl2_3),
% 0.23/0.51    inference(avatar_split_clause,[],[f23,f46])).
% 0.23/0.51  fof(f23,plain,(
% 0.23/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f5])).
% 0.23/0.51  fof(f5,axiom,(
% 0.23/0.51    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.23/0.51  fof(f44,plain,(
% 0.23/0.51    ~spl2_2),
% 0.23/0.51    inference(avatar_split_clause,[],[f22,f41])).
% 0.23/0.51  fof(f22,plain,(
% 0.23/0.51    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.23/0.51    inference(cnf_transformation,[],[f19])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f18])).
% 0.23/0.51  fof(f18,plain,(
% 0.23/0.51    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f13,plain,(
% 0.23/0.51    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f12])).
% 0.23/0.51  fof(f12,negated_conjecture,(
% 0.23/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.23/0.51    inference(negated_conjecture,[],[f11])).
% 0.23/0.51  fof(f11,conjecture,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.23/0.51  fof(f39,plain,(
% 0.23/0.51    spl2_1),
% 0.23/0.51    inference(avatar_split_clause,[],[f21,f36])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.51    inference(cnf_transformation,[],[f19])).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (12079)------------------------------
% 0.23/0.51  % (12079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (12079)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (12079)Memory used [KB]: 6396
% 0.23/0.51  % (12079)Time elapsed: 0.071 s
% 0.23/0.51  % (12079)------------------------------
% 0.23/0.51  % (12079)------------------------------
% 0.23/0.51  % (12073)Success in time 0.14 s
%------------------------------------------------------------------------------
