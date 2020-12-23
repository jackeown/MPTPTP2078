%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:15 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 205 expanded)
%              Number of leaves         :   23 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :  259 ( 493 expanded)
%              Number of equality atoms :   65 ( 132 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f474,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f66,f71,f86,f91,f107,f112,f122,f147,f152,f189,f236,f425,f468])).

fof(f468,plain,
    ( spl3_4
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_29 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | spl3_4
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f437,f85])).

fof(f85,plain,
    ( sK1 != k3_subset_1(sK0,sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_4
  <=> sK1 = k3_subset_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f437,plain,
    ( sK1 = k3_subset_1(sK0,sK2)
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_29 ),
    inference(backward_demodulation,[],[f121,f434])).

fof(f434,plain,
    ( sK2 = k4_xboole_0(sK0,sK1)
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_29 ),
    inference(backward_demodulation,[],[f235,f433])).

fof(f433,plain,
    ( sK2 = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)))
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f432,f188])).

fof(f188,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl3_15
  <=> sK2 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f432,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k3_xboole_0(sK0,sK2)
    | ~ spl3_12
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f430,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f430,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_12
    | ~ spl3_29 ),
    inference(superposition,[],[f164,f424])).

fof(f424,plain,
    ( k4_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl3_29
  <=> k4_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f164,plain,
    ( ! [X1] : k4_xboole_0(sK0,k2_xboole_0(sK1,X1)) = k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,X1)))
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f162,f163])).

fof(f163,plain,
    ( ! [X2] : k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK2),X2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,X2))
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f157,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f157,plain,
    ( ! [X2] : k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK2),X2)) = k4_xboole_0(k4_xboole_0(sK0,sK1),X2)
    | ~ spl3_12 ),
    inference(superposition,[],[f50,f146])).

fof(f146,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl3_12
  <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f162,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK2),X1)) = k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,X1)))
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f161,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f161,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK2),X1)) = k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,X1)))
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f156,f50])).

fof(f156,plain,
    ( ! [X1] : k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK2),X1)) = k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),X1))
    | ~ spl3_12 ),
    inference(superposition,[],[f51,f146])).

fof(f235,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl3_19
  <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f121,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_10
  <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f425,plain,
    ( spl3_29
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f347,f149,f109,f68,f57,f422])).

fof(f57,plain,
    ( spl3_1
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f68,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f109,plain,
    ( spl3_8
  <=> sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f149,plain,
    ( spl3_13
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f347,plain,
    ( k4_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f346,f50])).

fof(f346,plain,
    ( k4_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f345,f59])).

fof(f59,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f345,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | k4_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f340,f111])).

fof(f111,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f340,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,k4_xboole_0(sK0,sK2)))
    | k4_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(resolution,[],[f172,f151])).

fof(f151,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X0))
        | k2_xboole_0(sK1,k4_xboole_0(X0,sK1)) = X0 )
    | ~ spl3_3 ),
    inference(resolution,[],[f77,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f77,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X0)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f70,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2)
      | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

fof(f70,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f236,plain,
    ( spl3_19
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f153,f144,f233])).

fof(f153,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)))
    | ~ spl3_12 ),
    inference(superposition,[],[f146,f50])).

fof(f189,plain,
    ( spl3_15
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f178,f149,f109,f186])).

fof(f178,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f177,f111])).

fof(f177,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,sK2)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f175,f38])).

fof(f175,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_13 ),
    inference(resolution,[],[f151,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f152,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f127,f104,f63,f149])).

fof(f63,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f104,plain,
    ( spl3_7
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f127,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f125,f65])).

fof(f65,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f125,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_7 ),
    inference(superposition,[],[f43,f106])).

fof(f106,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f147,plain,
    ( spl3_12
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f92,f88,f144])).

fof(f88,plain,
    ( spl3_5
  <=> r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f92,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))
    | ~ spl3_5 ),
    inference(resolution,[],[f90,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f90,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f122,plain,
    ( spl3_10
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f80,f68,f119])).

fof(f80,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f78,f79])).

fof(f79,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f70,f44])).

fof(f78,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f70,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f112,plain,
    ( spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f75,f63,f109])).

fof(f75,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f73,f74])).

fof(f74,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f65,f44])).

fof(f73,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f65,f45])).

fof(f107,plain,
    ( spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f74,f63,f104])).

fof(f91,plain,
    ( spl3_5
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f81,f68,f63,f88])).

fof(f81,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f76,f79])).

fof(f76,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK2))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f32,f74])).

fof(f32,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
                & r1_xboole_0(X1,X2) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
              & r1_xboole_0(X1,X2) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

fof(f86,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f33,f83])).

fof(f33,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f63])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f31,f57])).

fof(f31,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:56:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (20734)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (20744)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (20757)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (20752)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (20741)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (20749)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (20739)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (20746)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (20745)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (20744)Refutation not found, incomplete strategy% (20744)------------------------------
% 0.22/0.52  % (20744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20744)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20744)Memory used [KB]: 10746
% 0.22/0.52  % (20744)Time elapsed: 0.102 s
% 0.22/0.52  % (20744)------------------------------
% 0.22/0.52  % (20744)------------------------------
% 0.22/0.52  % (20743)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (20748)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (20735)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (20751)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (20736)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (20747)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (20760)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (20756)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (20738)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (20759)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (20737)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (20756)Refutation not found, incomplete strategy% (20756)------------------------------
% 0.22/0.54  % (20756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20756)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20756)Memory used [KB]: 10746
% 0.22/0.54  % (20756)Time elapsed: 0.094 s
% 0.22/0.54  % (20756)------------------------------
% 0.22/0.54  % (20756)------------------------------
% 0.22/0.54  % (20743)Refutation not found, incomplete strategy% (20743)------------------------------
% 0.22/0.54  % (20743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20743)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20743)Memory used [KB]: 10746
% 0.22/0.54  % (20743)Time elapsed: 0.129 s
% 0.22/0.54  % (20743)------------------------------
% 0.22/0.54  % (20743)------------------------------
% 0.22/0.54  % (20753)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (20740)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (20762)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (20742)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (20754)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (20751)Refutation not found, incomplete strategy% (20751)------------------------------
% 0.22/0.55  % (20751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20751)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20751)Memory used [KB]: 10618
% 0.22/0.55  % (20751)Time elapsed: 0.143 s
% 0.22/0.55  % (20751)------------------------------
% 0.22/0.55  % (20751)------------------------------
% 0.22/0.55  % (20758)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (20763)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.55/0.56  % (20750)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.55/0.56  % (20755)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.55/0.56  % (20761)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.66/0.58  % (20754)Refutation found. Thanks to Tanya!
% 1.66/0.58  % SZS status Theorem for theBenchmark
% 1.66/0.58  % SZS output start Proof for theBenchmark
% 1.66/0.58  fof(f474,plain,(
% 1.66/0.58    $false),
% 1.66/0.58    inference(avatar_sat_refutation,[],[f60,f66,f71,f86,f91,f107,f112,f122,f147,f152,f189,f236,f425,f468])).
% 1.66/0.58  fof(f468,plain,(
% 1.66/0.58    spl3_4 | ~spl3_10 | ~spl3_12 | ~spl3_15 | ~spl3_19 | ~spl3_29),
% 1.66/0.58    inference(avatar_contradiction_clause,[],[f467])).
% 1.66/0.58  fof(f467,plain,(
% 1.66/0.58    $false | (spl3_4 | ~spl3_10 | ~spl3_12 | ~spl3_15 | ~spl3_19 | ~spl3_29)),
% 1.66/0.58    inference(subsumption_resolution,[],[f437,f85])).
% 1.66/0.58  fof(f85,plain,(
% 1.66/0.58    sK1 != k3_subset_1(sK0,sK2) | spl3_4),
% 1.66/0.58    inference(avatar_component_clause,[],[f83])).
% 1.66/0.58  fof(f83,plain,(
% 1.66/0.58    spl3_4 <=> sK1 = k3_subset_1(sK0,sK2)),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.66/0.58  fof(f437,plain,(
% 1.66/0.58    sK1 = k3_subset_1(sK0,sK2) | (~spl3_10 | ~spl3_12 | ~spl3_15 | ~spl3_19 | ~spl3_29)),
% 1.66/0.58    inference(backward_demodulation,[],[f121,f434])).
% 1.66/0.58  fof(f434,plain,(
% 1.66/0.58    sK2 = k4_xboole_0(sK0,sK1) | (~spl3_12 | ~spl3_15 | ~spl3_19 | ~spl3_29)),
% 1.66/0.58    inference(backward_demodulation,[],[f235,f433])).
% 1.66/0.58  fof(f433,plain,(
% 1.66/0.58    sK2 = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))) | (~spl3_12 | ~spl3_15 | ~spl3_29)),
% 1.66/0.58    inference(forward_demodulation,[],[f432,f188])).
% 1.66/0.58  fof(f188,plain,(
% 1.66/0.58    sK2 = k3_xboole_0(sK0,sK2) | ~spl3_15),
% 1.66/0.58    inference(avatar_component_clause,[],[f186])).
% 1.66/0.58  fof(f186,plain,(
% 1.66/0.58    spl3_15 <=> sK2 = k3_xboole_0(sK0,sK2)),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.66/0.58  fof(f432,plain,(
% 1.66/0.58    k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k3_xboole_0(sK0,sK2) | (~spl3_12 | ~spl3_29)),
% 1.66/0.58    inference(forward_demodulation,[],[f430,f38])).
% 1.66/0.58  fof(f38,plain,(
% 1.66/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f7])).
% 1.66/0.58  fof(f7,axiom,(
% 1.66/0.58    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.66/0.58  fof(f430,plain,(
% 1.66/0.58    k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_12 | ~spl3_29)),
% 1.66/0.58    inference(superposition,[],[f164,f424])).
% 1.66/0.58  fof(f424,plain,(
% 1.66/0.58    k4_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))) | ~spl3_29),
% 1.66/0.58    inference(avatar_component_clause,[],[f422])).
% 1.66/0.58  fof(f422,plain,(
% 1.66/0.58    spl3_29 <=> k4_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)))),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.66/0.58  fof(f164,plain,(
% 1.66/0.58    ( ! [X1] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X1)) = k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,X1)))) ) | ~spl3_12),
% 1.66/0.58    inference(backward_demodulation,[],[f162,f163])).
% 1.66/0.58  fof(f163,plain,(
% 1.66/0.58    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK2),X2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,X2))) ) | ~spl3_12),
% 1.66/0.58    inference(forward_demodulation,[],[f157,f50])).
% 1.66/0.58  fof(f50,plain,(
% 1.66/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f5])).
% 1.66/0.58  fof(f5,axiom,(
% 1.66/0.58    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.66/0.58  fof(f157,plain,(
% 1.66/0.58    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK2),X2)) = k4_xboole_0(k4_xboole_0(sK0,sK1),X2)) ) | ~spl3_12),
% 1.66/0.58    inference(superposition,[],[f50,f146])).
% 1.66/0.58  fof(f146,plain,(
% 1.66/0.58    k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) | ~spl3_12),
% 1.66/0.58    inference(avatar_component_clause,[],[f144])).
% 1.66/0.58  fof(f144,plain,(
% 1.66/0.58    spl3_12 <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.66/0.58  fof(f162,plain,(
% 1.66/0.58    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK2),X1)) = k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,X1)))) ) | ~spl3_12),
% 1.66/0.58    inference(forward_demodulation,[],[f161,f51])).
% 1.66/0.58  fof(f51,plain,(
% 1.66/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f8])).
% 1.66/0.58  fof(f8,axiom,(
% 1.66/0.58    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 1.66/0.58  fof(f161,plain,(
% 1.66/0.58    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK2),X1)) = k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,X1)))) ) | ~spl3_12),
% 1.66/0.58    inference(forward_demodulation,[],[f156,f50])).
% 1.66/0.58  fof(f156,plain,(
% 1.66/0.58    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK2),X1)) = k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),X1))) ) | ~spl3_12),
% 1.66/0.58    inference(superposition,[],[f51,f146])).
% 1.66/0.58  fof(f235,plain,(
% 1.66/0.58    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))) | ~spl3_19),
% 1.66/0.58    inference(avatar_component_clause,[],[f233])).
% 1.66/0.58  fof(f233,plain,(
% 1.66/0.58    spl3_19 <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)))),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.66/0.58  fof(f121,plain,(
% 1.66/0.58    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_10),
% 1.66/0.58    inference(avatar_component_clause,[],[f119])).
% 1.66/0.58  fof(f119,plain,(
% 1.66/0.58    spl3_10 <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.66/0.58  fof(f425,plain,(
% 1.66/0.58    spl3_29 | ~spl3_1 | ~spl3_3 | ~spl3_8 | ~spl3_13),
% 1.66/0.58    inference(avatar_split_clause,[],[f347,f149,f109,f68,f57,f422])).
% 1.66/0.58  fof(f57,plain,(
% 1.66/0.58    spl3_1 <=> r1_xboole_0(sK1,sK2)),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.66/0.58  fof(f68,plain,(
% 1.66/0.58    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.66/0.58  fof(f109,plain,(
% 1.66/0.58    spl3_8 <=> sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.66/0.58  fof(f149,plain,(
% 1.66/0.58    spl3_13 <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.66/0.58  fof(f347,plain,(
% 1.66/0.58    k4_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))) | (~spl3_1 | ~spl3_3 | ~spl3_8 | ~spl3_13)),
% 1.66/0.58    inference(forward_demodulation,[],[f346,f50])).
% 1.66/0.58  fof(f346,plain,(
% 1.66/0.58    k4_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) | (~spl3_1 | ~spl3_3 | ~spl3_8 | ~spl3_13)),
% 1.66/0.58    inference(subsumption_resolution,[],[f345,f59])).
% 1.66/0.58  fof(f59,plain,(
% 1.66/0.58    r1_xboole_0(sK1,sK2) | ~spl3_1),
% 1.66/0.58    inference(avatar_component_clause,[],[f57])).
% 1.66/0.58  fof(f345,plain,(
% 1.66/0.58    ~r1_xboole_0(sK1,sK2) | k4_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) | (~spl3_3 | ~spl3_8 | ~spl3_13)),
% 1.66/0.58    inference(forward_demodulation,[],[f340,f111])).
% 1.66/0.58  fof(f111,plain,(
% 1.66/0.58    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_8),
% 1.66/0.58    inference(avatar_component_clause,[],[f109])).
% 1.66/0.58  fof(f340,plain,(
% 1.66/0.58    ~r1_xboole_0(sK1,k3_subset_1(sK0,k4_xboole_0(sK0,sK2))) | k4_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) | (~spl3_3 | ~spl3_13)),
% 1.66/0.58    inference(resolution,[],[f172,f151])).
% 1.66/0.58  fof(f151,plain,(
% 1.66/0.58    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_13),
% 1.66/0.58    inference(avatar_component_clause,[],[f149])).
% 1.66/0.58  fof(f172,plain,(
% 1.66/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X0)) | k2_xboole_0(sK1,k4_xboole_0(X0,sK1)) = X0) ) | ~spl3_3),
% 1.66/0.58    inference(resolution,[],[f77,f41])).
% 1.66/0.58  fof(f41,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 1.66/0.58    inference(cnf_transformation,[],[f24])).
% 1.66/0.58  fof(f24,plain,(
% 1.66/0.58    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 1.66/0.58    inference(ennf_transformation,[],[f6])).
% 1.66/0.58  fof(f6,axiom,(
% 1.66/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 1.66/0.58  fof(f77,plain,(
% 1.66/0.58    ( ! [X0] : (r1_tarski(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X0))) ) | ~spl3_3),
% 1.66/0.58    inference(resolution,[],[f70,f47])).
% 1.66/0.58  fof(f47,plain,(
% 1.66/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f29])).
% 1.66/0.58  fof(f29,plain,(
% 1.66/0.58    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.66/0.58    inference(ennf_transformation,[],[f19])).
% 1.66/0.58  fof(f19,axiom,(
% 1.66/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).
% 1.66/0.58  fof(f70,plain,(
% 1.66/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 1.66/0.58    inference(avatar_component_clause,[],[f68])).
% 1.66/0.58  fof(f236,plain,(
% 1.66/0.58    spl3_19 | ~spl3_12),
% 1.66/0.58    inference(avatar_split_clause,[],[f153,f144,f233])).
% 1.66/0.58  fof(f153,plain,(
% 1.66/0.58    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))) | ~spl3_12),
% 1.66/0.58    inference(superposition,[],[f146,f50])).
% 1.66/0.58  fof(f189,plain,(
% 1.66/0.58    spl3_15 | ~spl3_8 | ~spl3_13),
% 1.66/0.58    inference(avatar_split_clause,[],[f178,f149,f109,f186])).
% 1.66/0.58  fof(f178,plain,(
% 1.66/0.58    sK2 = k3_xboole_0(sK0,sK2) | (~spl3_8 | ~spl3_13)),
% 1.66/0.58    inference(forward_demodulation,[],[f177,f111])).
% 1.66/0.58  fof(f177,plain,(
% 1.66/0.58    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,sK2) | ~spl3_13),
% 1.66/0.58    inference(forward_demodulation,[],[f175,f38])).
% 1.66/0.58  fof(f175,plain,(
% 1.66/0.58    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_13),
% 1.66/0.58    inference(resolution,[],[f151,f44])).
% 1.66/0.58  fof(f44,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f27])).
% 1.66/0.58  fof(f27,plain,(
% 1.66/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.66/0.58    inference(ennf_transformation,[],[f16])).
% 1.66/0.58  fof(f16,axiom,(
% 1.66/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.66/0.58  fof(f152,plain,(
% 1.66/0.58    spl3_13 | ~spl3_2 | ~spl3_7),
% 1.66/0.58    inference(avatar_split_clause,[],[f127,f104,f63,f149])).
% 1.66/0.58  fof(f63,plain,(
% 1.66/0.58    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.66/0.58  fof(f104,plain,(
% 1.66/0.58    spl3_7 <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.66/0.58  fof(f127,plain,(
% 1.66/0.58    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl3_2 | ~spl3_7)),
% 1.66/0.58    inference(subsumption_resolution,[],[f125,f65])).
% 1.66/0.58  fof(f65,plain,(
% 1.66/0.58    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.66/0.58    inference(avatar_component_clause,[],[f63])).
% 1.66/0.58  fof(f125,plain,(
% 1.66/0.58    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_7),
% 1.66/0.58    inference(superposition,[],[f43,f106])).
% 1.66/0.58  fof(f106,plain,(
% 1.66/0.58    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_7),
% 1.66/0.58    inference(avatar_component_clause,[],[f104])).
% 1.66/0.58  fof(f43,plain,(
% 1.66/0.58    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f26])).
% 1.66/0.58  fof(f26,plain,(
% 1.66/0.58    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.66/0.58    inference(ennf_transformation,[],[f17])).
% 1.66/0.58  fof(f17,axiom,(
% 1.66/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.66/0.58  fof(f147,plain,(
% 1.66/0.58    spl3_12 | ~spl3_5),
% 1.66/0.58    inference(avatar_split_clause,[],[f92,f88,f144])).
% 1.66/0.58  fof(f88,plain,(
% 1.66/0.58    spl3_5 <=> r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.66/0.58  fof(f92,plain,(
% 1.66/0.58    k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) | ~spl3_5),
% 1.66/0.58    inference(resolution,[],[f90,f49])).
% 1.66/0.58  fof(f49,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.66/0.58    inference(cnf_transformation,[],[f9])).
% 1.66/0.58  fof(f9,axiom,(
% 1.66/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.66/0.58  fof(f90,plain,(
% 1.66/0.58    r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) | ~spl3_5),
% 1.66/0.58    inference(avatar_component_clause,[],[f88])).
% 1.66/0.58  fof(f122,plain,(
% 1.66/0.58    spl3_10 | ~spl3_3),
% 1.66/0.58    inference(avatar_split_clause,[],[f80,f68,f119])).
% 1.66/0.58  fof(f80,plain,(
% 1.66/0.58    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_3),
% 1.66/0.58    inference(backward_demodulation,[],[f78,f79])).
% 1.66/0.58  fof(f79,plain,(
% 1.66/0.58    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_3),
% 1.66/0.58    inference(resolution,[],[f70,f44])).
% 1.66/0.58  fof(f78,plain,(
% 1.66/0.58    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_3),
% 1.66/0.58    inference(resolution,[],[f70,f45])).
% 1.66/0.58  fof(f45,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.66/0.58    inference(cnf_transformation,[],[f28])).
% 1.66/0.58  fof(f28,plain,(
% 1.66/0.58    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.66/0.58    inference(ennf_transformation,[],[f18])).
% 1.66/0.58  fof(f18,axiom,(
% 1.66/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.66/0.58  fof(f112,plain,(
% 1.66/0.58    spl3_8 | ~spl3_2),
% 1.66/0.58    inference(avatar_split_clause,[],[f75,f63,f109])).
% 1.66/0.58  fof(f75,plain,(
% 1.66/0.58    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_2),
% 1.66/0.58    inference(backward_demodulation,[],[f73,f74])).
% 1.66/0.58  fof(f74,plain,(
% 1.66/0.58    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_2),
% 1.66/0.58    inference(resolution,[],[f65,f44])).
% 1.66/0.58  fof(f73,plain,(
% 1.66/0.58    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | ~spl3_2),
% 1.66/0.58    inference(resolution,[],[f65,f45])).
% 1.66/0.58  fof(f107,plain,(
% 1.66/0.58    spl3_7 | ~spl3_2),
% 1.66/0.58    inference(avatar_split_clause,[],[f74,f63,f104])).
% 1.66/0.58  fof(f91,plain,(
% 1.66/0.58    spl3_5 | ~spl3_2 | ~spl3_3),
% 1.66/0.58    inference(avatar_split_clause,[],[f81,f68,f63,f88])).
% 1.66/0.58  fof(f81,plain,(
% 1.66/0.58    r1_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) | (~spl3_2 | ~spl3_3)),
% 1.66/0.58    inference(backward_demodulation,[],[f76,f79])).
% 1.66/0.58  fof(f76,plain,(
% 1.66/0.58    r1_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK2)) | ~spl3_2),
% 1.66/0.58    inference(backward_demodulation,[],[f32,f74])).
% 1.66/0.58  fof(f32,plain,(
% 1.66/0.58    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))),
% 1.66/0.58    inference(cnf_transformation,[],[f23])).
% 1.66/0.58  fof(f23,plain,(
% 1.66/0.58    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.66/0.58    inference(flattening,[],[f22])).
% 1.66/0.58  fof(f22,plain,(
% 1.66/0.58    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & (r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.66/0.58    inference(ennf_transformation,[],[f21])).
% 1.66/0.58  fof(f21,negated_conjecture,(
% 1.66/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 1.66/0.58    inference(negated_conjecture,[],[f20])).
% 1.66/0.58  fof(f20,conjecture,(
% 1.66/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).
% 1.66/0.58  fof(f86,plain,(
% 1.66/0.58    ~spl3_4),
% 1.66/0.58    inference(avatar_split_clause,[],[f33,f83])).
% 1.66/0.58  fof(f33,plain,(
% 1.66/0.58    sK1 != k3_subset_1(sK0,sK2)),
% 1.66/0.58    inference(cnf_transformation,[],[f23])).
% 1.66/0.58  fof(f71,plain,(
% 1.66/0.58    spl3_3),
% 1.66/0.58    inference(avatar_split_clause,[],[f34,f68])).
% 1.66/0.58  fof(f34,plain,(
% 1.66/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.66/0.58    inference(cnf_transformation,[],[f23])).
% 1.66/0.58  fof(f66,plain,(
% 1.66/0.58    spl3_2),
% 1.66/0.58    inference(avatar_split_clause,[],[f30,f63])).
% 1.66/0.58  fof(f30,plain,(
% 1.66/0.58    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.66/0.58    inference(cnf_transformation,[],[f23])).
% 1.66/0.58  fof(f60,plain,(
% 1.66/0.58    spl3_1),
% 1.66/0.58    inference(avatar_split_clause,[],[f31,f57])).
% 1.66/0.58  fof(f31,plain,(
% 1.66/0.58    r1_xboole_0(sK1,sK2)),
% 1.66/0.58    inference(cnf_transformation,[],[f23])).
% 1.66/0.58  % SZS output end Proof for theBenchmark
% 1.66/0.58  % (20754)------------------------------
% 1.66/0.58  % (20754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (20754)Termination reason: Refutation
% 1.66/0.58  
% 1.66/0.58  % (20754)Memory used [KB]: 11129
% 1.66/0.58  % (20754)Time elapsed: 0.173 s
% 1.66/0.58  % (20754)------------------------------
% 1.66/0.58  % (20754)------------------------------
% 1.66/0.58  % (20733)Success in time 0.217 s
%------------------------------------------------------------------------------
