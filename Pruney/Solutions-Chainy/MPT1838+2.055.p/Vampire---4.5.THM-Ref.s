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
% DateTime   : Thu Dec  3 13:20:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 201 expanded)
%              Number of leaves         :   26 (  81 expanded)
%              Depth                    :   10
%              Number of atoms          :  305 ( 529 expanded)
%              Number of equality atoms :   76 ( 129 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f263,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f61,f74,f79,f95,f101,f117,f130,f135,f152,f164,f170,f243,f250,f262])).

fof(f262,plain,
    ( spl3_1
    | ~ spl3_17
    | ~ spl3_31
    | ~ spl3_32 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | spl3_1
    | ~ spl3_17
    | ~ spl3_31
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f260,f242])).

fof(f242,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl3_31
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f260,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl3_1
    | ~ spl3_17
    | ~ spl3_32 ),
    inference(resolution,[],[f200,f249])).

fof(f249,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl3_32
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | spl3_1
    | ~ spl3_17 ),
    inference(superposition,[],[f63,f148])).

fof(f148,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_17
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f63,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(sK1,X1)
        | ~ r1_tarski(sK1,X1) )
    | spl3_1 ),
    inference(resolution,[],[f40,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f40,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f250,plain,
    ( spl3_32
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f245,f146,f114,f247])).

fof(f114,plain,
    ( spl3_13
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f245,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f244,f148])).

fof(f244,plain,
    ( r1_xboole_0(sK1,sK1)
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f124,f148])).

fof(f124,plain,
    ( k1_xboole_0 != sK1
    | r1_xboole_0(sK1,sK1)
    | ~ spl3_13 ),
    inference(superposition,[],[f32,f116])).

fof(f116,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f243,plain,
    ( spl3_31
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f207,f146,f132,f240])).

fof(f132,plain,
    ( spl3_15
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f207,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(superposition,[],[f134,f148])).

fof(f134,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f170,plain,
    ( ~ spl3_14
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(trivial_inequality_removal,[],[f168])).

fof(f168,plain,
    ( sK1 != sK1
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(superposition,[],[f151,f129])).

fof(f129,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_14
  <=> sK1 = k1_tarski(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f151,plain,
    ( ! [X0] : k1_tarski(X0) != sK1
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_18
  <=> ! [X0] : k1_tarski(X0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f164,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl3_3
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f161,f55])).

fof(f55,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f161,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f90,f66])).

fof(f66,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        | ~ r1_tarski(sK0,X1) )
    | spl3_3 ),
    inference(resolution,[],[f50,f29])).

fof(f50,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f90,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_8
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f152,plain,
    ( spl3_17
    | spl3_18
    | spl3_5
    | ~ spl3_7
    | spl3_9 ),
    inference(avatar_split_clause,[],[f144,f92,f76,f58,f150,f146])).

fof(f58,plain,
    ( spl3_5
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f76,plain,
    ( spl3_7
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f92,plain,
    ( spl3_9
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f144,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != sK1
        | k1_xboole_0 = sK1 )
    | spl3_5
    | ~ spl3_7
    | spl3_9 ),
    inference(subsumption_resolution,[],[f85,f94])).

fof(f94,plain,
    ( k1_xboole_0 != sK0
    | spl3_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f85,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != sK1
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK1 )
    | spl3_5
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f83,f60])).

fof(f60,plain,
    ( sK0 != sK1
    | spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f83,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != sK1
        | sK0 = sK1
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK1 )
    | ~ spl3_7 ),
    inference(superposition,[],[f36,f78])).

fof(f78,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | X1 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f135,plain,
    ( spl3_15
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f125,f114,f132])).

fof(f125,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl3_13 ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK1)
    | ~ spl3_13 ),
    inference(superposition,[],[f35,f116])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f130,plain,
    ( spl3_14
    | spl3_1
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f121,f98,f43,f38,f127])).

fof(f43,plain,
    ( spl3_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f98,plain,
    ( spl3_10
  <=> sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f121,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f120,f100])).

fof(f100,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f98])).

fof(f120,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f119,f45])).

fof(f45,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f119,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | ~ v1_zfmisc_1(sK1)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f118,f40])).

fof(f118,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ v1_zfmisc_1(sK1)
    | spl3_1 ),
    inference(resolution,[],[f62,f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f62,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_tarski(X0) = k6_domain_1(sK1,X0) )
    | spl3_1 ),
    inference(resolution,[],[f40,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f117,plain,
    ( spl3_13
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f86,f76,f71,f114])).

fof(f71,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f86,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f84,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f84,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK1)
    | ~ spl3_7 ),
    inference(superposition,[],[f28,f78])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f101,plain,
    ( spl3_10
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f96,f43,f38,f98])).

fof(f96,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f64,f45])).

fof(f64,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ v1_zfmisc_1(sK1)
    | spl3_1 ),
    inference(resolution,[],[f40,f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f95,plain,
    ( spl3_8
    | ~ spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f81,f71,f92,f88])).

fof(f81,plain,
    ( k1_xboole_0 != sK0
    | r1_xboole_0(sK0,sK1)
    | ~ spl3_6 ),
    inference(superposition,[],[f32,f73])).

fof(f79,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f69,f53,f76])).

fof(f69,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f55,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f74,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f68,f53,f71])).

fof(f68,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f55,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f61,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f56,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f24,f48])).

fof(f24,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f43])).

fof(f21,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f38])).

fof(f20,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:12:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (24046)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.44  % (24046)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f263,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f61,f74,f79,f95,f101,f117,f130,f135,f152,f164,f170,f243,f250,f262])).
% 0.21/0.44  fof(f262,plain,(
% 0.21/0.44    spl3_1 | ~spl3_17 | ~spl3_31 | ~spl3_32),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f261])).
% 0.21/0.44  fof(f261,plain,(
% 0.21/0.44    $false | (spl3_1 | ~spl3_17 | ~spl3_31 | ~spl3_32)),
% 0.21/0.44    inference(subsumption_resolution,[],[f260,f242])).
% 0.21/0.44  fof(f242,plain,(
% 0.21/0.44    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl3_31),
% 0.21/0.44    inference(avatar_component_clause,[],[f240])).
% 0.21/0.44  fof(f240,plain,(
% 0.21/0.44    spl3_31 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.44  fof(f260,plain,(
% 0.21/0.44    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl3_1 | ~spl3_17 | ~spl3_32)),
% 0.21/0.44    inference(resolution,[],[f200,f249])).
% 0.21/0.44  fof(f249,plain,(
% 0.21/0.44    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_32),
% 0.21/0.44    inference(avatar_component_clause,[],[f247])).
% 0.21/0.44  fof(f247,plain,(
% 0.21/0.44    spl3_32 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.44  fof(f200,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,X0)) ) | (spl3_1 | ~spl3_17)),
% 0.21/0.44    inference(superposition,[],[f63,f148])).
% 0.21/0.44  fof(f148,plain,(
% 0.21/0.44    k1_xboole_0 = sK1 | ~spl3_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f146])).
% 0.21/0.44  fof(f146,plain,(
% 0.21/0.44    spl3_17 <=> k1_xboole_0 = sK1),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    ( ! [X1] : (~r1_xboole_0(sK1,X1) | ~r1_tarski(sK1,X1)) ) | spl3_1),
% 0.21/0.44    inference(resolution,[],[f40,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.44    inference(flattening,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ~v1_xboole_0(sK1) | spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    spl3_1 <=> v1_xboole_0(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f250,plain,(
% 0.21/0.44    spl3_32 | ~spl3_13 | ~spl3_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f245,f146,f114,f247])).
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    spl3_13 <=> k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.44  fof(f245,plain,(
% 0.21/0.44    r1_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_13 | ~spl3_17)),
% 0.21/0.44    inference(forward_demodulation,[],[f244,f148])).
% 0.21/0.44  fof(f244,plain,(
% 0.21/0.44    r1_xboole_0(sK1,sK1) | (~spl3_13 | ~spl3_17)),
% 0.21/0.44    inference(subsumption_resolution,[],[f124,f148])).
% 0.21/0.44  fof(f124,plain,(
% 0.21/0.44    k1_xboole_0 != sK1 | r1_xboole_0(sK1,sK1) | ~spl3_13),
% 0.21/0.44    inference(superposition,[],[f32,f116])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(sK1,sK1) | ~spl3_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f114])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.44  fof(f243,plain,(
% 0.21/0.44    spl3_31 | ~spl3_15 | ~spl3_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f207,f146,f132,f240])).
% 0.21/0.44  fof(f132,plain,(
% 0.21/0.44    spl3_15 <=> r1_tarski(sK1,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.44  fof(f207,plain,(
% 0.21/0.44    r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl3_15 | ~spl3_17)),
% 0.21/0.44    inference(superposition,[],[f134,f148])).
% 0.21/0.44  fof(f134,plain,(
% 0.21/0.44    r1_tarski(sK1,sK1) | ~spl3_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f132])).
% 0.21/0.44  fof(f170,plain,(
% 0.21/0.44    ~spl3_14 | ~spl3_18),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f169])).
% 0.21/0.44  fof(f169,plain,(
% 0.21/0.44    $false | (~spl3_14 | ~spl3_18)),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f168])).
% 0.21/0.44  fof(f168,plain,(
% 0.21/0.44    sK1 != sK1 | (~spl3_14 | ~spl3_18)),
% 0.21/0.44    inference(superposition,[],[f151,f129])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    sK1 = k1_tarski(sK2(sK1)) | ~spl3_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f127])).
% 0.21/0.44  fof(f127,plain,(
% 0.21/0.44    spl3_14 <=> sK1 = k1_tarski(sK2(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.44  fof(f151,plain,(
% 0.21/0.44    ( ! [X0] : (k1_tarski(X0) != sK1) ) | ~spl3_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f150])).
% 0.21/0.44  fof(f150,plain,(
% 0.21/0.44    spl3_18 <=> ! [X0] : k1_tarski(X0) != sK1),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.44  fof(f164,plain,(
% 0.21/0.44    spl3_3 | ~spl3_4 | ~spl3_8),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f163])).
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    $false | (spl3_3 | ~spl3_4 | ~spl3_8)),
% 0.21/0.44    inference(subsumption_resolution,[],[f161,f55])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    r1_tarski(sK0,sK1) | ~spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f53])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    spl3_4 <=> r1_tarski(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f161,plain,(
% 0.21/0.44    ~r1_tarski(sK0,sK1) | (spl3_3 | ~spl3_8)),
% 0.21/0.44    inference(resolution,[],[f90,f66])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ( ! [X1] : (~r1_xboole_0(sK0,X1) | ~r1_tarski(sK0,X1)) ) | spl3_3),
% 0.21/0.44    inference(resolution,[],[f50,f29])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ~v1_xboole_0(sK0) | spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f48])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    spl3_3 <=> v1_xboole_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    r1_xboole_0(sK0,sK1) | ~spl3_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f88])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    spl3_8 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.44  fof(f152,plain,(
% 0.21/0.44    spl3_17 | spl3_18 | spl3_5 | ~spl3_7 | spl3_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f144,f92,f76,f58,f150,f146])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    spl3_5 <=> sK0 = sK1),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    spl3_7 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    spl3_9 <=> k1_xboole_0 = sK0),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    ( ! [X0] : (k1_tarski(X0) != sK1 | k1_xboole_0 = sK1) ) | (spl3_5 | ~spl3_7 | spl3_9)),
% 0.21/0.44    inference(subsumption_resolution,[],[f85,f94])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    k1_xboole_0 != sK0 | spl3_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f92])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    ( ! [X0] : (k1_tarski(X0) != sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) ) | (spl3_5 | ~spl3_7)),
% 0.21/0.44    inference(subsumption_resolution,[],[f83,f60])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    sK0 != sK1 | spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f58])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    ( ! [X0] : (k1_tarski(X0) != sK1 | sK0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) ) | ~spl3_7),
% 0.21/0.44    inference(superposition,[],[f36,f78])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f76])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | X1 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.21/0.44  fof(f135,plain,(
% 0.21/0.44    spl3_15 | ~spl3_13),
% 0.21/0.44    inference(avatar_split_clause,[],[f125,f114,f132])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    r1_tarski(sK1,sK1) | ~spl3_13),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f123])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK1) | ~spl3_13),
% 0.21/0.44    inference(superposition,[],[f35,f116])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    spl3_14 | spl3_1 | ~spl3_2 | ~spl3_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f121,f98,f43,f38,f127])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    spl3_2 <=> v1_zfmisc_1(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f98,plain,(
% 0.21/0.44    spl3_10 <=> sK1 = k6_domain_1(sK1,sK2(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    sK1 = k1_tarski(sK2(sK1)) | (spl3_1 | ~spl3_2 | ~spl3_10)),
% 0.21/0.44    inference(forward_demodulation,[],[f120,f100])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    sK1 = k6_domain_1(sK1,sK2(sK1)) | ~spl3_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f98])).
% 0.21/0.44  fof(f120,plain,(
% 0.21/0.44    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | (spl3_1 | ~spl3_2)),
% 0.21/0.44    inference(subsumption_resolution,[],[f119,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    v1_zfmisc_1(sK1) | ~spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f43])).
% 0.21/0.44  fof(f119,plain,(
% 0.21/0.44    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | ~v1_zfmisc_1(sK1) | spl3_1),
% 0.21/0.44    inference(subsumption_resolution,[],[f118,f40])).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1) | spl3_1),
% 0.21/0.44    inference(resolution,[],[f62,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_tarski(X0) = k6_domain_1(sK1,X0)) ) | spl3_1),
% 0.21/0.44    inference(resolution,[],[f40,f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.44    inference(flattening,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    spl3_13 | ~spl3_6 | ~spl3_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f86,f76,f71,f114])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(sK1,sK1) | (~spl3_6 | ~spl3_7)),
% 0.21/0.44    inference(forward_demodulation,[],[f84,f73])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f71])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK1) | ~spl3_7),
% 0.21/0.44    inference(superposition,[],[f28,f78])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    spl3_10 | spl3_1 | ~spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f96,f43,f38,f98])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    sK1 = k6_domain_1(sK1,sK2(sK1)) | (spl3_1 | ~spl3_2)),
% 0.21/0.44    inference(subsumption_resolution,[],[f64,f45])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    sK1 = k6_domain_1(sK1,sK2(sK1)) | ~v1_zfmisc_1(sK1) | spl3_1),
% 0.21/0.44    inference(resolution,[],[f40,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    spl3_8 | ~spl3_9 | ~spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f81,f71,f92,f88])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    k1_xboole_0 != sK0 | r1_xboole_0(sK0,sK1) | ~spl3_6),
% 0.21/0.44    inference(superposition,[],[f32,f73])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    spl3_7 | ~spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f69,f53,f76])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_4),
% 0.21/0.44    inference(resolution,[],[f55,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    spl3_6 | ~spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f68,f53,f71])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_4),
% 0.21/0.44    inference(resolution,[],[f55,f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    ~spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f23,f58])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    sK0 != sK1),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.44    inference(flattening,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.44    inference(negated_conjecture,[],[f9])).
% 0.21/0.44  fof(f9,conjecture,(
% 0.21/0.44    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f53])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    r1_tarski(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ~spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f24,f48])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ~v1_xboole_0(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f43])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    v1_zfmisc_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ~spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f38])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ~v1_xboole_0(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (24046)------------------------------
% 0.21/0.44  % (24046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (24046)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (24046)Memory used [KB]: 10746
% 0.21/0.44  % (24046)Time elapsed: 0.059 s
% 0.21/0.44  % (24046)------------------------------
% 0.21/0.44  % (24046)------------------------------
% 0.21/0.44  % (24042)Success in time 0.089 s
%------------------------------------------------------------------------------
