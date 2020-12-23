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
% DateTime   : Thu Dec  3 12:44:51 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 184 expanded)
%              Number of leaves         :   29 (  75 expanded)
%              Depth                    :    7
%              Number of atoms          :  254 ( 425 expanded)
%              Number of equality atoms :   35 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f540,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f111,f243,f253,f255,f259,f270,f274,f283,f288,f297,f512,f522])).

fof(f522,plain,
    ( spl5_1
    | ~ spl5_24
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f521,f509,f280,f59])).

fof(f59,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f280,plain,
    ( spl5_24
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f509,plain,
    ( spl5_50
  <=> sK0 = k3_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f521,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_24
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f513,f155])).

fof(f155,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f148,f52])).

fof(f52,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f32,f51])).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f31,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f32,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f148,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f42,f33])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f513,plain,
    ( sK1 = k3_subset_1(sK0,sK0)
    | ~ spl5_24
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f282,f511])).

fof(f511,plain,
    ( sK0 = k3_subset_1(sK0,sK1)
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f509])).

fof(f282,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f280])).

fof(f512,plain,
    ( spl5_50
    | ~ spl5_25
    | ~ spl5_26
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f499,f280,f294,f285,f509])).

fof(f285,plain,
    ( spl5_25
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f294,plain,
    ( spl5_26
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f499,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | sK0 = k3_subset_1(sK0,sK1)
    | ~ spl5_24 ),
    inference(superposition,[],[f190,f282])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1 ) ),
    inference(forward_demodulation,[],[f53,f52])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k1_xboole_0) = X1
      | ~ r1_tarski(k3_subset_1(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f44,f51])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_subset_1(X0) = X1
      | ~ r1_tarski(k3_subset_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f297,plain,
    ( spl5_26
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f289,f236,f69,f294])).

fof(f69,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f236,plain,
    ( spl5_20
  <=> r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f289,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(resolution,[],[f238,f121])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f50,f71])).

fof(f71,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f238,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f236])).

fof(f288,plain,
    ( spl5_25
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f276,f240,f285])).

fof(f240,plain,
    ( spl5_21
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f276,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_21 ),
    inference(resolution,[],[f241,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f241,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f240])).

fof(f283,plain,
    ( spl5_24
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f275,f240,f280])).

fof(f275,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl5_21 ),
    inference(resolution,[],[f241,f42])).

fof(f274,plain,
    ( spl5_21
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f272,f267,f240])).

fof(f267,plain,
    ( spl5_23
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f272,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_23 ),
    inference(resolution,[],[f269,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f36,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f269,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f267])).

fof(f270,plain,
    ( spl5_23
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f265,f247,f267])).

fof(f247,plain,
    ( spl5_22
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f265,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_22 ),
    inference(resolution,[],[f249,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f249,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f247])).

fof(f259,plain,
    ( spl5_22
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f256,f128,f69,f247])).

fof(f128,plain,
    ( spl5_10
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f256,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(resolution,[],[f130,f121])).

fof(f130,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f255,plain,
    ( spl5_10
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f124,f108,f128])).

fof(f108,plain,
    ( spl5_8
  <=> r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f124,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f110,f56])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f110,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f253,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl5_7 ),
    inference(resolution,[],[f106,f30])).

fof(f30,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f106,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_7
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f243,plain,
    ( spl5_20
    | ~ spl5_21
    | ~ spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f228,f64,f74,f240,f236])).

fof(f74,plain,
    ( spl5_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f64,plain,
    ( spl5_2
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f228,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f45,f66])).

fof(f66,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X2,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(f111,plain,
    ( spl5_7
    | spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f99,f74,f108,f104])).

fof(f99,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f40,f76])).

fof(f76,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f26,f74])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f72,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f27,f69])).

fof(f27,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 13:34:15 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (4007)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (3999)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (3991)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (3989)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.37/0.54  % (4003)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.54  % (3987)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.54  % (3984)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.54  % (3986)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.54  % (4012)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.54  % (3985)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.37/0.54  % (3988)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.54  % (3994)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.54  % (4013)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.37/0.55  % (4011)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.55  % (4008)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.37/0.55  % (4005)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.37/0.55  % (4009)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.37/0.55  % (4005)Refutation not found, incomplete strategy% (4005)------------------------------
% 1.37/0.55  % (4005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (4005)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (4005)Memory used [KB]: 1663
% 1.37/0.55  % (4005)Time elapsed: 0.150 s
% 1.37/0.55  % (4005)------------------------------
% 1.37/0.55  % (4005)------------------------------
% 1.37/0.55  % (3997)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.37/0.55  % (4010)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.37/0.55  % (4004)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.55  % (3995)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.56/0.55  % (3992)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.56/0.55  % (4004)Refutation not found, incomplete strategy% (4004)------------------------------
% 1.56/0.55  % (4004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.55  % (4004)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.55  
% 1.56/0.55  % (4004)Memory used [KB]: 10746
% 1.56/0.55  % (4004)Time elapsed: 0.148 s
% 1.56/0.55  % (4004)------------------------------
% 1.56/0.55  % (4004)------------------------------
% 1.56/0.56  % (4000)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.56/0.56  % (3996)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.56  % (4002)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.56/0.56  % (4001)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.56/0.56  % (4001)Refutation not found, incomplete strategy% (4001)------------------------------
% 1.56/0.56  % (4001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (4001)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.56  
% 1.56/0.56  % (4001)Memory used [KB]: 10618
% 1.56/0.56  % (4001)Time elapsed: 0.147 s
% 1.56/0.56  % (4001)------------------------------
% 1.56/0.56  % (4001)------------------------------
% 1.56/0.56  % (4000)Refutation found. Thanks to Tanya!
% 1.56/0.56  % SZS status Theorem for theBenchmark
% 1.56/0.56  % SZS output start Proof for theBenchmark
% 1.56/0.56  fof(f540,plain,(
% 1.56/0.56    $false),
% 1.56/0.56    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f111,f243,f253,f255,f259,f270,f274,f283,f288,f297,f512,f522])).
% 1.56/0.56  fof(f522,plain,(
% 1.56/0.56    spl5_1 | ~spl5_24 | ~spl5_50),
% 1.56/0.56    inference(avatar_split_clause,[],[f521,f509,f280,f59])).
% 1.56/0.56  fof(f59,plain,(
% 1.56/0.56    spl5_1 <=> k1_xboole_0 = sK1),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.56/0.56  fof(f280,plain,(
% 1.56/0.56    spl5_24 <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.56/0.56  fof(f509,plain,(
% 1.56/0.56    spl5_50 <=> sK0 = k3_subset_1(sK0,sK1)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 1.56/0.56  fof(f521,plain,(
% 1.56/0.56    k1_xboole_0 = sK1 | (~spl5_24 | ~spl5_50)),
% 1.56/0.56    inference(forward_demodulation,[],[f513,f155])).
% 1.56/0.56  fof(f155,plain,(
% 1.56/0.56    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f148,f52])).
% 1.56/0.56  fof(f52,plain,(
% 1.56/0.56    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.56/0.56    inference(definition_unfolding,[],[f32,f51])).
% 1.56/0.56  fof(f51,plain,(
% 1.56/0.56    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.56/0.56    inference(definition_unfolding,[],[f34,f31])).
% 1.56/0.56  fof(f31,plain,(
% 1.56/0.56    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 1.56/0.56    inference(cnf_transformation,[],[f5])).
% 1.56/0.56  fof(f5,axiom,(
% 1.56/0.56    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.56/0.56  fof(f34,plain,(
% 1.56/0.56    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f10])).
% 1.56/0.56  fof(f10,axiom,(
% 1.56/0.56    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 1.56/0.56  fof(f32,plain,(
% 1.56/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.56/0.56    inference(cnf_transformation,[],[f6])).
% 1.56/0.56  fof(f6,axiom,(
% 1.56/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.56/0.56  fof(f148,plain,(
% 1.56/0.56    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 1.56/0.56    inference(resolution,[],[f42,f33])).
% 1.56/0.56  fof(f33,plain,(
% 1.56/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f13])).
% 1.56/0.56  fof(f13,axiom,(
% 1.56/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.56/0.56  fof(f42,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.56/0.56    inference(cnf_transformation,[],[f20])).
% 1.56/0.56  fof(f20,plain,(
% 1.56/0.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.56    inference(ennf_transformation,[],[f9])).
% 1.56/0.56  fof(f9,axiom,(
% 1.56/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.56/0.56  fof(f513,plain,(
% 1.56/0.56    sK1 = k3_subset_1(sK0,sK0) | (~spl5_24 | ~spl5_50)),
% 1.56/0.56    inference(backward_demodulation,[],[f282,f511])).
% 1.56/0.56  fof(f511,plain,(
% 1.56/0.56    sK0 = k3_subset_1(sK0,sK1) | ~spl5_50),
% 1.56/0.56    inference(avatar_component_clause,[],[f509])).
% 1.56/0.56  fof(f282,plain,(
% 1.56/0.56    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl5_24),
% 1.56/0.56    inference(avatar_component_clause,[],[f280])).
% 1.56/0.56  fof(f512,plain,(
% 1.56/0.56    spl5_50 | ~spl5_25 | ~spl5_26 | ~spl5_24),
% 1.56/0.56    inference(avatar_split_clause,[],[f499,f280,f294,f285,f509])).
% 1.56/0.56  fof(f285,plain,(
% 1.56/0.56    spl5_25 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.56/0.56  fof(f294,plain,(
% 1.56/0.56    spl5_26 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.56/0.56  fof(f499,plain,(
% 1.56/0.56    ~r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | sK0 = k3_subset_1(sK0,sK1) | ~spl5_24),
% 1.56/0.56    inference(superposition,[],[f190,f282])).
% 1.56/0.56  fof(f190,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1) )),
% 1.56/0.56    inference(forward_demodulation,[],[f53,f52])).
% 1.56/0.56  fof(f53,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k1_xboole_0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) )),
% 1.56/0.56    inference(definition_unfolding,[],[f44,f51])).
% 1.56/0.56  fof(f44,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f21])).
% 1.56/0.56  fof(f21,plain,(
% 1.56/0.56    ! [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.56    inference(ennf_transformation,[],[f12])).
% 1.56/0.56  fof(f12,axiom,(
% 1.56/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 1.56/0.56  fof(f297,plain,(
% 1.56/0.56    spl5_26 | ~spl5_3 | ~spl5_20),
% 1.56/0.56    inference(avatar_split_clause,[],[f289,f236,f69,f294])).
% 1.56/0.56  fof(f69,plain,(
% 1.56/0.56    spl5_3 <=> r1_tarski(sK1,sK2)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.56/0.56  fof(f236,plain,(
% 1.56/0.56    spl5_20 <=> r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.56/0.56  fof(f289,plain,(
% 1.56/0.56    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | (~spl5_3 | ~spl5_20)),
% 1.56/0.56    inference(resolution,[],[f238,f121])).
% 1.56/0.56  fof(f121,plain,(
% 1.56/0.56    ( ! [X0] : (~r1_tarski(sK2,X0) | r1_tarski(sK1,X0)) ) | ~spl5_3),
% 1.56/0.56    inference(resolution,[],[f50,f71])).
% 1.56/0.56  fof(f71,plain,(
% 1.56/0.56    r1_tarski(sK1,sK2) | ~spl5_3),
% 1.56/0.56    inference(avatar_component_clause,[],[f69])).
% 1.56/0.56  fof(f50,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f25])).
% 1.56/0.56  fof(f25,plain,(
% 1.56/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.56/0.56    inference(flattening,[],[f24])).
% 1.56/0.56  fof(f24,plain,(
% 1.56/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.56/0.56    inference(ennf_transformation,[],[f2])).
% 1.56/0.56  fof(f2,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.56/0.56  fof(f238,plain,(
% 1.56/0.56    r1_tarski(sK2,k3_subset_1(sK0,sK1)) | ~spl5_20),
% 1.56/0.56    inference(avatar_component_clause,[],[f236])).
% 1.56/0.56  fof(f288,plain,(
% 1.56/0.56    spl5_25 | ~spl5_21),
% 1.56/0.56    inference(avatar_split_clause,[],[f276,f240,f285])).
% 1.56/0.56  fof(f240,plain,(
% 1.56/0.56    spl5_21 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.56/0.56  fof(f276,plain,(
% 1.56/0.56    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl5_21),
% 1.56/0.56    inference(resolution,[],[f241,f41])).
% 1.56/0.56  fof(f41,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f19])).
% 1.56/0.56  fof(f19,plain,(
% 1.56/0.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.56    inference(ennf_transformation,[],[f7])).
% 1.56/0.56  fof(f7,axiom,(
% 1.56/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.56/0.56  fof(f241,plain,(
% 1.56/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_21),
% 1.56/0.56    inference(avatar_component_clause,[],[f240])).
% 1.56/0.56  fof(f283,plain,(
% 1.56/0.56    spl5_24 | ~spl5_21),
% 1.56/0.56    inference(avatar_split_clause,[],[f275,f240,f280])).
% 1.56/0.56  fof(f275,plain,(
% 1.56/0.56    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl5_21),
% 1.56/0.56    inference(resolution,[],[f241,f42])).
% 1.56/0.56  fof(f274,plain,(
% 1.56/0.56    spl5_21 | ~spl5_23),
% 1.56/0.56    inference(avatar_split_clause,[],[f272,f267,f240])).
% 1.56/0.56  fof(f267,plain,(
% 1.56/0.56    spl5_23 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.56/0.56  fof(f272,plain,(
% 1.56/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_23),
% 1.56/0.56    inference(resolution,[],[f269,f78])).
% 1.56/0.56  fof(f78,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.56/0.56    inference(global_subsumption,[],[f36,f39])).
% 1.56/0.56  fof(f39,plain,(
% 1.56/0.56    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f18])).
% 1.56/0.56  fof(f18,plain,(
% 1.56/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.56/0.56    inference(ennf_transformation,[],[f4])).
% 1.56/0.56  fof(f4,axiom,(
% 1.56/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.56/0.56  fof(f36,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f1])).
% 1.56/0.56  fof(f1,axiom,(
% 1.56/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.56/0.56  fof(f269,plain,(
% 1.56/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_23),
% 1.56/0.56    inference(avatar_component_clause,[],[f267])).
% 1.56/0.56  fof(f270,plain,(
% 1.56/0.56    spl5_23 | ~spl5_22),
% 1.56/0.56    inference(avatar_split_clause,[],[f265,f247,f267])).
% 1.56/0.56  fof(f247,plain,(
% 1.56/0.56    spl5_22 <=> r1_tarski(sK1,sK0)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.56/0.56  fof(f265,plain,(
% 1.56/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_22),
% 1.56/0.56    inference(resolution,[],[f249,f57])).
% 1.56/0.56  fof(f57,plain,(
% 1.56/0.56    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.56/0.56    inference(equality_resolution,[],[f46])).
% 1.56/0.56  fof(f46,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.56/0.56    inference(cnf_transformation,[],[f3])).
% 1.56/0.56  fof(f3,axiom,(
% 1.56/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.56/0.56  fof(f249,plain,(
% 1.56/0.56    r1_tarski(sK1,sK0) | ~spl5_22),
% 1.56/0.56    inference(avatar_component_clause,[],[f247])).
% 1.56/0.56  fof(f259,plain,(
% 1.56/0.56    spl5_22 | ~spl5_3 | ~spl5_10),
% 1.56/0.56    inference(avatar_split_clause,[],[f256,f128,f69,f247])).
% 1.56/0.56  fof(f128,plain,(
% 1.56/0.56    spl5_10 <=> r1_tarski(sK2,sK0)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.56/0.56  fof(f256,plain,(
% 1.56/0.56    r1_tarski(sK1,sK0) | (~spl5_3 | ~spl5_10)),
% 1.56/0.56    inference(resolution,[],[f130,f121])).
% 1.56/0.56  fof(f130,plain,(
% 1.56/0.56    r1_tarski(sK2,sK0) | ~spl5_10),
% 1.56/0.56    inference(avatar_component_clause,[],[f128])).
% 1.56/0.56  fof(f255,plain,(
% 1.56/0.56    spl5_10 | ~spl5_8),
% 1.56/0.56    inference(avatar_split_clause,[],[f124,f108,f128])).
% 1.56/0.56  fof(f108,plain,(
% 1.56/0.56    spl5_8 <=> r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.56/0.56  fof(f124,plain,(
% 1.56/0.56    r1_tarski(sK2,sK0) | ~spl5_8),
% 1.56/0.56    inference(resolution,[],[f110,f56])).
% 1.56/0.56  fof(f56,plain,(
% 1.56/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.56/0.56    inference(equality_resolution,[],[f47])).
% 1.56/0.56  fof(f47,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.56/0.56    inference(cnf_transformation,[],[f3])).
% 1.56/0.56  fof(f110,plain,(
% 1.56/0.56    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl5_8),
% 1.56/0.56    inference(avatar_component_clause,[],[f108])).
% 1.56/0.56  fof(f253,plain,(
% 1.56/0.56    ~spl5_7),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f251])).
% 1.56/0.56  fof(f251,plain,(
% 1.56/0.56    $false | ~spl5_7),
% 1.56/0.56    inference(resolution,[],[f106,f30])).
% 1.56/0.56  fof(f30,plain,(
% 1.56/0.56    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f8])).
% 1.56/0.56  fof(f8,axiom,(
% 1.56/0.56    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.56/0.56  fof(f106,plain,(
% 1.56/0.56    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_7),
% 1.56/0.56    inference(avatar_component_clause,[],[f104])).
% 1.56/0.56  fof(f104,plain,(
% 1.56/0.56    spl5_7 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.56/0.56  fof(f243,plain,(
% 1.56/0.56    spl5_20 | ~spl5_21 | ~spl5_4 | ~spl5_2),
% 1.56/0.56    inference(avatar_split_clause,[],[f228,f64,f74,f240,f236])).
% 1.56/0.56  fof(f74,plain,(
% 1.56/0.56    spl5_4 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.56/0.56  fof(f64,plain,(
% 1.56/0.56    spl5_2 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.56/0.56  fof(f228,plain,(
% 1.56/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | r1_tarski(sK2,k3_subset_1(sK0,sK1)) | ~spl5_2),
% 1.56/0.56    inference(resolution,[],[f45,f66])).
% 1.56/0.56  fof(f66,plain,(
% 1.56/0.56    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~spl5_2),
% 1.56/0.56    inference(avatar_component_clause,[],[f64])).
% 1.56/0.56  fof(f45,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X2,k3_subset_1(X0,X1))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f23])).
% 1.56/0.56  fof(f23,plain,(
% 1.56/0.56    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.56    inference(flattening,[],[f22])).
% 1.56/0.56  fof(f22,plain,(
% 1.56/0.56    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.56    inference(ennf_transformation,[],[f11])).
% 1.56/0.56  fof(f11,axiom,(
% 1.56/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).
% 1.56/0.56  fof(f111,plain,(
% 1.56/0.56    spl5_7 | spl5_8 | ~spl5_4),
% 1.56/0.56    inference(avatar_split_clause,[],[f99,f74,f108,f104])).
% 1.56/0.56  fof(f99,plain,(
% 1.56/0.56    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_4),
% 1.56/0.56    inference(resolution,[],[f40,f76])).
% 1.56/0.56  fof(f76,plain,(
% 1.56/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl5_4),
% 1.56/0.56    inference(avatar_component_clause,[],[f74])).
% 1.56/0.56  fof(f40,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f18])).
% 1.56/0.56  fof(f77,plain,(
% 1.56/0.56    spl5_4),
% 1.56/0.56    inference(avatar_split_clause,[],[f26,f74])).
% 1.56/0.56  fof(f26,plain,(
% 1.56/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.56/0.56    inference(cnf_transformation,[],[f17])).
% 1.56/0.56  fof(f17,plain,(
% 1.56/0.56    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.56/0.56    inference(flattening,[],[f16])).
% 1.56/0.56  fof(f16,plain,(
% 1.56/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.56/0.56    inference(ennf_transformation,[],[f15])).
% 1.56/0.56  fof(f15,negated_conjecture,(
% 1.56/0.56    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.56/0.56    inference(negated_conjecture,[],[f14])).
% 1.56/0.56  fof(f14,conjecture,(
% 1.56/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 1.56/0.56  fof(f72,plain,(
% 1.56/0.56    spl5_3),
% 1.56/0.56    inference(avatar_split_clause,[],[f27,f69])).
% 1.56/0.56  fof(f27,plain,(
% 1.56/0.56    r1_tarski(sK1,sK2)),
% 1.56/0.56    inference(cnf_transformation,[],[f17])).
% 1.56/0.56  fof(f67,plain,(
% 1.56/0.56    spl5_2),
% 1.56/0.56    inference(avatar_split_clause,[],[f28,f64])).
% 1.56/0.56  fof(f28,plain,(
% 1.56/0.56    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.56/0.56    inference(cnf_transformation,[],[f17])).
% 1.56/0.56  fof(f62,plain,(
% 1.56/0.56    ~spl5_1),
% 1.56/0.56    inference(avatar_split_clause,[],[f29,f59])).
% 1.56/0.56  fof(f29,plain,(
% 1.56/0.56    k1_xboole_0 != sK1),
% 1.56/0.56    inference(cnf_transformation,[],[f17])).
% 1.56/0.56  % SZS output end Proof for theBenchmark
% 1.56/0.56  % (4000)------------------------------
% 1.56/0.56  % (4000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (4000)Termination reason: Refutation
% 1.56/0.56  
% 1.56/0.56  % (4000)Memory used [KB]: 11001
% 1.56/0.56  % (4000)Time elapsed: 0.152 s
% 1.56/0.56  % (4000)------------------------------
% 1.56/0.56  % (4000)------------------------------
% 1.56/0.56  % (3993)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.56/0.57  % (3990)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.56/0.59  % (3983)Success in time 0.225 s
%------------------------------------------------------------------------------
