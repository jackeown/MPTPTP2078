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
% DateTime   : Thu Dec  3 12:46:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 191 expanded)
%              Number of leaves         :   28 (  79 expanded)
%              Depth                    :    8
%              Number of atoms          :  278 ( 478 expanded)
%              Number of equality atoms :   55 (  95 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f385,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f50,f55,f78,f94,f99,f109,f115,f136,f153,f218,f253,f273,f281,f285,f344,f369,f381,f384])).

fof(f384,plain,
    ( k1_xboole_0 != sK1
    | sK0 != k8_setfam_1(sK0,k1_xboole_0)
    | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f381,plain,
    ( spl3_35
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f371,f366,f378])).

fof(f378,plain,
    ( spl3_35
  <=> sK0 = k8_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f366,plain,
    ( spl3_34
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f371,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl3_34 ),
    inference(resolution,[],[f368,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f368,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f366])).

fof(f369,plain,
    ( spl3_34
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f290,f146,f52,f366])).

fof(f52,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f146,plain,
    ( spl3_17
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f290,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3
    | ~ spl3_17 ),
    inference(superposition,[],[f54,f148])).

fof(f148,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f54,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f344,plain,
    ( ~ spl3_14
    | spl3_29 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl3_14
    | spl3_29 ),
    inference(subsumption_resolution,[],[f328,f37])).

fof(f37,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f328,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_14
    | spl3_29 ),
    inference(superposition,[],[f272,f131])).

fof(f131,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_14
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f272,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl3_29
  <=> r1_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f285,plain,
    ( ~ spl3_1
    | spl3_17
    | spl3_30 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl3_1
    | spl3_17
    | spl3_30 ),
    inference(subsumption_resolution,[],[f283,f42])).

fof(f42,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f283,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_17
    | spl3_30 ),
    inference(subsumption_resolution,[],[f282,f147])).

fof(f147,plain,
    ( k1_xboole_0 != sK1
    | spl3_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f282,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | spl3_30 ),
    inference(resolution,[],[f280,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f280,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl3_30
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f281,plain,
    ( ~ spl3_30
    | spl3_6
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f248,f150,f133,f75,f278])).

fof(f75,plain,
    ( spl3_6
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f133,plain,
    ( spl3_15
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f150,plain,
    ( spl3_18
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f248,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_6
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f247,f152])).

fof(f152,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f150])).

fof(f247,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl3_6
    | ~ spl3_15 ),
    inference(superposition,[],[f77,f135])).

fof(f135,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f133])).

fof(f77,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f273,plain,
    ( ~ spl3_29
    | ~ spl3_1
    | spl3_27 ),
    inference(avatar_split_clause,[],[f255,f250,f40,f270])).

fof(f250,plain,
    ( spl3_27
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f255,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | ~ spl3_1
    | spl3_27 ),
    inference(resolution,[],[f252,f44])).

fof(f44,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK1,X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f42,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f252,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl3_27 ),
    inference(avatar_component_clause,[],[f250])).

fof(f253,plain,
    ( ~ spl3_27
    | spl3_24 ),
    inference(avatar_split_clause,[],[f219,f215,f250])).

fof(f215,plain,
    ( spl3_24
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f219,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl3_24 ),
    inference(resolution,[],[f217,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f217,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl3_24 ),
    inference(avatar_component_clause,[],[f215])).

fof(f218,plain,
    ( ~ spl3_24
    | ~ spl3_1
    | spl3_17 ),
    inference(avatar_split_clause,[],[f213,f146,f40,f215])).

fof(f213,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | ~ spl3_1
    | spl3_17 ),
    inference(subsumption_resolution,[],[f89,f147])).

fof(f89,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ spl3_1 ),
    inference(resolution,[],[f44,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f153,plain,
    ( spl3_17
    | spl3_18
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f125,f106,f52,f150,f146])).

fof(f106,plain,
    ( spl3_11
  <=> k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f125,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | k1_xboole_0 = sK1
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f65,f108])).

fof(f108,plain,
    ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f65,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f54,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f136,plain,
    ( spl3_14
    | spl3_15
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f124,f96,f47,f133,f129])).

fof(f47,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f96,plain,
    ( spl3_9
  <=> k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f124,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f56,f98])).

fof(f98,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f56,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f49,f33])).

fof(f49,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f115,plain,
    ( spl3_12
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f110,f91,f112])).

fof(f112,plain,
    ( spl3_12
  <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f91,plain,
    ( spl3_8
  <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f110,plain,
    ( r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f93,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f93,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f109,plain,
    ( spl3_11
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f67,f52,f106])).

fof(f67,plain,
    ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f54,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f99,plain,
    ( spl3_9
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f58,f47,f96])).

fof(f58,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f49,f30])).

fof(f94,plain,
    ( spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f57,f47,f91])).

fof(f57,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f49,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f78,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f24,f75])).

fof(f24,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f55,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:31:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (9159)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (9150)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (9158)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.47  % (9161)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (9151)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (9157)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (9158)Refutation not found, incomplete strategy% (9158)------------------------------
% 0.20/0.48  % (9158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9158)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (9158)Memory used [KB]: 10618
% 0.20/0.48  % (9157)Refutation not found, incomplete strategy% (9157)------------------------------
% 0.20/0.48  % (9157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9157)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (9157)Memory used [KB]: 6012
% 0.20/0.48  % (9157)Time elapsed: 0.056 s
% 0.20/0.48  % (9157)------------------------------
% 0.20/0.48  % (9157)------------------------------
% 0.20/0.48  % (9158)Time elapsed: 0.068 s
% 0.20/0.48  % (9158)------------------------------
% 0.20/0.48  % (9158)------------------------------
% 0.20/0.48  % (9160)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (9153)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (9165)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.48  % (9150)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f385,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f43,f50,f55,f78,f94,f99,f109,f115,f136,f153,f218,f253,f273,f281,f285,f344,f369,f381,f384])).
% 0.20/0.48  fof(f384,plain,(
% 0.20/0.48    k1_xboole_0 != sK1 | sK0 != k8_setfam_1(sK0,k1_xboole_0) | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | ~r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 0.20/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.48  fof(f381,plain,(
% 0.20/0.48    spl3_35 | ~spl3_34),
% 0.20/0.48    inference(avatar_split_clause,[],[f371,f366,f378])).
% 0.20/0.48  fof(f378,plain,(
% 0.20/0.48    spl3_35 <=> sK0 = k8_setfam_1(sK0,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.48  fof(f366,plain,(
% 0.20/0.48    spl3_34 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.48  fof(f371,plain,(
% 0.20/0.48    sK0 = k8_setfam_1(sK0,k1_xboole_0) | ~spl3_34),
% 0.20/0.48    inference(resolution,[],[f368,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.48    inference(equality_resolution,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.20/0.48  fof(f368,plain,(
% 0.20/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_34),
% 0.20/0.48    inference(avatar_component_clause,[],[f366])).
% 0.20/0.48  fof(f369,plain,(
% 0.20/0.48    spl3_34 | ~spl3_3 | ~spl3_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f290,f146,f52,f366])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    spl3_17 <=> k1_xboole_0 = sK1),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.48  fof(f290,plain,(
% 0.20/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_3 | ~spl3_17)),
% 0.20/0.48    inference(superposition,[],[f54,f148])).
% 0.20/0.48  fof(f148,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | ~spl3_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f146])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f52])).
% 0.20/0.48  fof(f344,plain,(
% 0.20/0.48    ~spl3_14 | spl3_29),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f343])).
% 0.20/0.48  fof(f343,plain,(
% 0.20/0.48    $false | (~spl3_14 | spl3_29)),
% 0.20/0.48    inference(subsumption_resolution,[],[f328,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.48    inference(equality_resolution,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.20/0.48  fof(f328,plain,(
% 0.20/0.48    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_14 | spl3_29)),
% 0.20/0.48    inference(superposition,[],[f272,f131])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | ~spl3_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f129])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    spl3_14 <=> k1_xboole_0 = sK2),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.48  fof(f272,plain,(
% 0.20/0.48    ~r1_xboole_0(sK2,sK2) | spl3_29),
% 0.20/0.48    inference(avatar_component_clause,[],[f270])).
% 0.20/0.48  fof(f270,plain,(
% 0.20/0.48    spl3_29 <=> r1_xboole_0(sK2,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.48  fof(f285,plain,(
% 0.20/0.48    ~spl3_1 | spl3_17 | spl3_30),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f284])).
% 0.20/0.48  fof(f284,plain,(
% 0.20/0.48    $false | (~spl3_1 | spl3_17 | spl3_30)),
% 0.20/0.48    inference(subsumption_resolution,[],[f283,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    r1_tarski(sK1,sK2) | ~spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    spl3_1 <=> r1_tarski(sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f283,plain,(
% 0.20/0.48    ~r1_tarski(sK1,sK2) | (spl3_17 | spl3_30)),
% 0.20/0.48    inference(subsumption_resolution,[],[f282,f147])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    k1_xboole_0 != sK1 | spl3_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f146])).
% 0.20/0.48  fof(f282,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | spl3_30),
% 0.20/0.48    inference(resolution,[],[f280,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.20/0.48  fof(f280,plain,(
% 0.20/0.48    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl3_30),
% 0.20/0.48    inference(avatar_component_clause,[],[f278])).
% 0.20/0.48  fof(f278,plain,(
% 0.20/0.48    spl3_30 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.48  fof(f281,plain,(
% 0.20/0.48    ~spl3_30 | spl3_6 | ~spl3_15 | ~spl3_18),
% 0.20/0.48    inference(avatar_split_clause,[],[f248,f150,f133,f75,f278])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    spl3_6 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    spl3_15 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    spl3_18 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.48  fof(f248,plain,(
% 0.20/0.48    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (spl3_6 | ~spl3_15 | ~spl3_18)),
% 0.20/0.48    inference(forward_demodulation,[],[f247,f152])).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f150])).
% 0.20/0.48  fof(f247,plain,(
% 0.20/0.48    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | (spl3_6 | ~spl3_15)),
% 0.20/0.48    inference(superposition,[],[f77,f135])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f133])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl3_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f75])).
% 0.20/0.48  fof(f273,plain,(
% 0.20/0.48    ~spl3_29 | ~spl3_1 | spl3_27),
% 0.20/0.48    inference(avatar_split_clause,[],[f255,f250,f40,f270])).
% 0.20/0.48  fof(f250,plain,(
% 0.20/0.48    spl3_27 <=> r1_xboole_0(sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.48  fof(f255,plain,(
% 0.20/0.48    ~r1_xboole_0(sK2,sK2) | (~spl3_1 | spl3_27)),
% 0.20/0.48    inference(resolution,[],[f252,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0] : (r1_xboole_0(sK1,X0) | ~r1_xboole_0(sK2,X0)) ) | ~spl3_1),
% 0.20/0.48    inference(resolution,[],[f42,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.48  fof(f252,plain,(
% 0.20/0.48    ~r1_xboole_0(sK1,sK2) | spl3_27),
% 0.20/0.48    inference(avatar_component_clause,[],[f250])).
% 0.20/0.48  fof(f253,plain,(
% 0.20/0.48    ~spl3_27 | spl3_24),
% 0.20/0.48    inference(avatar_split_clause,[],[f219,f215,f250])).
% 0.20/0.48  fof(f215,plain,(
% 0.20/0.48    spl3_24 <=> r1_xboole_0(sK2,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.48  fof(f219,plain,(
% 0.20/0.48    ~r1_xboole_0(sK1,sK2) | spl3_24),
% 0.20/0.48    inference(resolution,[],[f217,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.48  fof(f217,plain,(
% 0.20/0.48    ~r1_xboole_0(sK2,sK1) | spl3_24),
% 0.20/0.48    inference(avatar_component_clause,[],[f215])).
% 0.20/0.48  fof(f218,plain,(
% 0.20/0.48    ~spl3_24 | ~spl3_1 | spl3_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f213,f146,f40,f215])).
% 0.20/0.48  fof(f213,plain,(
% 0.20/0.48    ~r1_xboole_0(sK2,sK1) | (~spl3_1 | spl3_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f89,f147])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    ~r1_xboole_0(sK2,sK1) | k1_xboole_0 = sK1 | ~spl3_1),
% 0.20/0.48    inference(resolution,[],[f44,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    spl3_17 | spl3_18 | ~spl3_3 | ~spl3_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f125,f106,f52,f150,f146])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    spl3_11 <=> k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | k1_xboole_0 = sK1 | (~spl3_3 | ~spl3_11)),
% 0.20/0.48    inference(forward_demodulation,[],[f65,f108])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f106])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) | ~spl3_3),
% 0.20/0.48    inference(resolution,[],[f54,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    spl3_14 | spl3_15 | ~spl3_2 | ~spl3_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f124,f96,f47,f133,f129])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    spl3_9 <=> k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2 | (~spl3_2 | ~spl3_9)),
% 0.20/0.48    inference(forward_demodulation,[],[f56,f98])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f96])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) | ~spl3_2),
% 0.20/0.48    inference(resolution,[],[f49,f33])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f47])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    spl3_12 | ~spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f110,f91,f112])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    spl3_12 <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    spl3_8 <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~spl3_8),
% 0.20/0.48    inference(resolution,[],[f93,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f91])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    spl3_11 | ~spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f67,f52,f106])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_3),
% 0.20/0.48    inference(resolution,[],[f54,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    spl3_9 | ~spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f58,f47,f96])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_2),
% 0.20/0.48    inference(resolution,[],[f49,f30])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    spl3_8 | ~spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f57,f47,f91])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.20/0.48    inference(resolution,[],[f49,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ~spl3_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f24,f75])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f9])).
% 0.20/0.48  fof(f9,conjecture,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f25,f52])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f22,f47])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    spl3_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f23,f40])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    r1_tarski(sK1,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (9150)------------------------------
% 0.20/0.48  % (9150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9150)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (9150)Memory used [KB]: 10746
% 0.20/0.48  % (9150)Time elapsed: 0.065 s
% 0.20/0.48  % (9150)------------------------------
% 0.20/0.48  % (9150)------------------------------
% 0.20/0.48  % (9146)Success in time 0.117 s
%------------------------------------------------------------------------------
