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
% DateTime   : Thu Dec  3 12:44:51 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 187 expanded)
%              Number of leaves         :   29 (  76 expanded)
%              Depth                    :    7
%              Number of atoms          :  255 ( 428 expanded)
%              Number of equality atoms :   35 (  74 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f541,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f112,f244,f254,f256,f260,f271,f275,f284,f289,f298,f513,f523])).

fof(f523,plain,
    ( spl5_1
    | ~ spl5_24
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f522,f510,f281,f60])).

fof(f60,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f281,plain,
    ( spl5_24
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f510,plain,
    ( spl5_50
  <=> sK0 = k3_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f522,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_24
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f514,f156])).

fof(f156,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f149,f52])).

fof(f52,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f31,f51])).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f34,f32])).

fof(f32,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f31,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f149,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f42,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f514,plain,
    ( sK1 = k3_subset_1(sK0,sK0)
    | ~ spl5_24
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f283,f512])).

fof(f512,plain,
    ( sK0 = k3_subset_1(sK0,sK1)
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f510])).

fof(f283,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f281])).

fof(f513,plain,
    ( spl5_50
    | ~ spl5_25
    | ~ spl5_26
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f500,f281,f295,f286,f510])).

fof(f286,plain,
    ( spl5_25
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f295,plain,
    ( spl5_26
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f500,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | sK0 = k3_subset_1(sK0,sK1)
    | ~ spl5_24 ),
    inference(superposition,[],[f191,f283])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1 ) ),
    inference(forward_demodulation,[],[f54,f52])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f298,plain,
    ( spl5_26
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f290,f237,f70,f295])).

fof(f70,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f237,plain,
    ( spl5_20
  <=> r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f290,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(resolution,[],[f239,f122])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f50,f72])).

fof(f72,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f70])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f239,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f237])).

fof(f289,plain,
    ( spl5_25
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f277,f241,f286])).

fof(f241,plain,
    ( spl5_21
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f277,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_21 ),
    inference(resolution,[],[f242,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f242,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f241])).

fof(f284,plain,
    ( spl5_24
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f276,f241,f281])).

fof(f276,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl5_21 ),
    inference(resolution,[],[f242,f42])).

fof(f275,plain,
    ( spl5_21
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f273,f268,f241])).

fof(f268,plain,
    ( spl5_23
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f273,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_23 ),
    inference(resolution,[],[f270,f79])).

fof(f79,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f270,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f268])).

fof(f271,plain,
    ( spl5_23
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f266,f248,f268])).

fof(f248,plain,
    ( spl5_22
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f266,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_22 ),
    inference(resolution,[],[f250,f58])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f250,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f248])).

fof(f260,plain,
    ( spl5_22
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f257,f129,f70,f248])).

fof(f129,plain,
    ( spl5_10
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f257,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(resolution,[],[f131,f122])).

fof(f131,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f256,plain,
    ( spl5_10
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f125,f109,f129])).

fof(f109,plain,
    ( spl5_8
  <=> r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f125,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f111,f57])).

fof(f57,plain,(
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

fof(f111,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f254,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl5_7 ),
    inference(resolution,[],[f107,f30])).

fof(f30,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f107,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_7
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f244,plain,
    ( spl5_20
    | ~ spl5_21
    | ~ spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f229,f65,f75,f241,f237])).

fof(f75,plain,
    ( spl5_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f65,plain,
    ( spl5_2
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f229,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f45,f67])).

fof(f67,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f112,plain,
    ( spl5_7
    | spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f100,f75,f109,f105])).

fof(f100,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f40,f77])).

fof(f77,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f26,f75])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f73,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f27,f70])).

fof(f27,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f28,f65])).

fof(f28,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.31/0.57  % (25218)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.31/0.57  % (25205)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.57  % (25216)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.57  % (25224)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.58  % (25204)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.58  % (25230)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.58  % (25214)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.31/0.58  % (25220)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.59  % (25213)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.31/0.59  % (25226)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.59  % (25226)Refutation not found, incomplete strategy% (25226)------------------------------
% 1.31/0.59  % (25226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.59  % (25226)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.59  
% 1.31/0.59  % (25226)Memory used [KB]: 10746
% 1.31/0.59  % (25226)Time elapsed: 0.155 s
% 1.31/0.59  % (25226)------------------------------
% 1.31/0.59  % (25226)------------------------------
% 1.31/0.60  % (25223)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.61  % (25224)Refutation not found, incomplete strategy% (25224)------------------------------
% 1.31/0.61  % (25224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.61  % (25224)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.61  
% 1.31/0.61  % (25224)Memory used [KB]: 10746
% 1.31/0.61  % (25224)Time elapsed: 0.160 s
% 1.31/0.61  % (25224)------------------------------
% 1.31/0.61  % (25224)------------------------------
% 1.31/0.61  % (25219)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.61  % (25209)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.61  % (25212)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.31/0.62  % (25206)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.63  % (25217)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.31/0.63  % (25235)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.63  % (25208)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.63  % (25211)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.63  % (25220)Refutation found. Thanks to Tanya!
% 1.31/0.63  % SZS status Theorem for theBenchmark
% 1.31/0.63  % SZS output start Proof for theBenchmark
% 1.31/0.63  fof(f541,plain,(
% 1.31/0.63    $false),
% 1.31/0.63    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f112,f244,f254,f256,f260,f271,f275,f284,f289,f298,f513,f523])).
% 1.31/0.63  fof(f523,plain,(
% 1.31/0.63    spl5_1 | ~spl5_24 | ~spl5_50),
% 1.31/0.63    inference(avatar_split_clause,[],[f522,f510,f281,f60])).
% 1.31/0.63  fof(f60,plain,(
% 1.31/0.63    spl5_1 <=> k1_xboole_0 = sK1),
% 1.31/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.31/0.63  fof(f281,plain,(
% 1.31/0.63    spl5_24 <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 1.31/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.31/0.63  fof(f510,plain,(
% 1.31/0.63    spl5_50 <=> sK0 = k3_subset_1(sK0,sK1)),
% 1.31/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 1.31/0.63  fof(f522,plain,(
% 1.31/0.63    k1_xboole_0 = sK1 | (~spl5_24 | ~spl5_50)),
% 1.31/0.63    inference(forward_demodulation,[],[f514,f156])).
% 1.31/0.63  fof(f156,plain,(
% 1.31/0.63    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.31/0.63    inference(forward_demodulation,[],[f149,f52])).
% 1.31/0.63  fof(f52,plain,(
% 1.31/0.63    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.31/0.63    inference(definition_unfolding,[],[f31,f51])).
% 1.31/0.63  fof(f51,plain,(
% 1.31/0.63    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.31/0.63    inference(definition_unfolding,[],[f34,f32])).
% 1.31/0.63  fof(f32,plain,(
% 1.31/0.63    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 1.31/0.63    inference(cnf_transformation,[],[f5])).
% 1.31/0.63  fof(f5,axiom,(
% 1.31/0.63    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 1.31/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.31/0.63  fof(f34,plain,(
% 1.31/0.63    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.31/0.63    inference(cnf_transformation,[],[f11])).
% 1.31/0.63  fof(f11,axiom,(
% 1.31/0.63    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.31/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 1.31/0.63  fof(f31,plain,(
% 1.31/0.63    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.31/0.63    inference(cnf_transformation,[],[f6])).
% 1.31/0.63  fof(f6,axiom,(
% 1.31/0.63    ! [X0] : k2_subset_1(X0) = X0),
% 1.31/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.31/0.63  fof(f149,plain,(
% 1.31/0.63    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 1.31/0.63    inference(resolution,[],[f42,f53])).
% 1.31/0.63  fof(f53,plain,(
% 1.31/0.63    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.31/0.63    inference(definition_unfolding,[],[f33,f32])).
% 1.31/0.63  fof(f33,plain,(
% 1.31/0.63    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.31/0.63    inference(cnf_transformation,[],[f7])).
% 1.31/0.63  fof(f7,axiom,(
% 1.31/0.63    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 1.31/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 1.31/0.63  fof(f42,plain,(
% 1.31/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.31/0.63    inference(cnf_transformation,[],[f20])).
% 1.31/0.63  fof(f20,plain,(
% 1.31/0.63    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.31/0.63    inference(ennf_transformation,[],[f10])).
% 1.31/0.63  fof(f10,axiom,(
% 1.31/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.31/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.31/0.63  fof(f514,plain,(
% 1.31/0.63    sK1 = k3_subset_1(sK0,sK0) | (~spl5_24 | ~spl5_50)),
% 1.31/0.63    inference(backward_demodulation,[],[f283,f512])).
% 1.31/0.63  fof(f512,plain,(
% 1.31/0.63    sK0 = k3_subset_1(sK0,sK1) | ~spl5_50),
% 1.31/0.63    inference(avatar_component_clause,[],[f510])).
% 1.31/0.63  fof(f283,plain,(
% 1.31/0.63    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl5_24),
% 1.31/0.63    inference(avatar_component_clause,[],[f281])).
% 1.31/0.63  fof(f513,plain,(
% 1.31/0.63    spl5_50 | ~spl5_25 | ~spl5_26 | ~spl5_24),
% 1.31/0.63    inference(avatar_split_clause,[],[f500,f281,f295,f286,f510])).
% 1.31/0.63  fof(f286,plain,(
% 1.31/0.63    spl5_25 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.31/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.31/0.63  fof(f295,plain,(
% 1.31/0.63    spl5_26 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.31/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.31/0.63  fof(f500,plain,(
% 1.31/0.63    ~r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | sK0 = k3_subset_1(sK0,sK1) | ~spl5_24),
% 1.31/0.63    inference(superposition,[],[f191,f283])).
% 1.31/0.63  fof(f191,plain,(
% 1.31/0.63    ( ! [X0,X1] : (~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1) )),
% 1.31/0.63    inference(forward_demodulation,[],[f54,f52])).
% 1.31/0.63  fof(f54,plain,(
% 1.31/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k1_xboole_0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) )),
% 1.31/0.63    inference(definition_unfolding,[],[f44,f51])).
% 1.31/0.63  fof(f44,plain,(
% 1.31/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) )),
% 1.31/0.63    inference(cnf_transformation,[],[f21])).
% 1.31/0.63  fof(f21,plain,(
% 1.31/0.63    ! [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.31/0.63    inference(ennf_transformation,[],[f13])).
% 1.31/0.63  fof(f13,axiom,(
% 1.31/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.31/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 1.31/0.63  fof(f298,plain,(
% 1.31/0.63    spl5_26 | ~spl5_3 | ~spl5_20),
% 1.31/0.63    inference(avatar_split_clause,[],[f290,f237,f70,f295])).
% 1.31/0.63  fof(f70,plain,(
% 1.31/0.63    spl5_3 <=> r1_tarski(sK1,sK2)),
% 1.31/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.31/0.63  fof(f237,plain,(
% 1.31/0.63    spl5_20 <=> r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 1.31/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.31/0.63  fof(f290,plain,(
% 1.31/0.63    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | (~spl5_3 | ~spl5_20)),
% 1.31/0.63    inference(resolution,[],[f239,f122])).
% 1.31/0.63  fof(f122,plain,(
% 1.31/0.63    ( ! [X0] : (~r1_tarski(sK2,X0) | r1_tarski(sK1,X0)) ) | ~spl5_3),
% 1.31/0.63    inference(resolution,[],[f50,f72])).
% 1.31/0.63  fof(f72,plain,(
% 1.31/0.63    r1_tarski(sK1,sK2) | ~spl5_3),
% 1.31/0.63    inference(avatar_component_clause,[],[f70])).
% 1.31/0.63  fof(f50,plain,(
% 1.31/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.31/0.63    inference(cnf_transformation,[],[f25])).
% 1.31/0.63  fof(f25,plain,(
% 1.31/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.31/0.63    inference(flattening,[],[f24])).
% 1.31/0.63  fof(f24,plain,(
% 1.31/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.31/0.63    inference(ennf_transformation,[],[f2])).
% 1.31/0.63  fof(f2,axiom,(
% 1.31/0.63    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.31/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.31/0.64  fof(f239,plain,(
% 1.31/0.64    r1_tarski(sK2,k3_subset_1(sK0,sK1)) | ~spl5_20),
% 1.31/0.64    inference(avatar_component_clause,[],[f237])).
% 1.31/0.64  fof(f289,plain,(
% 1.31/0.64    spl5_25 | ~spl5_21),
% 1.31/0.64    inference(avatar_split_clause,[],[f277,f241,f286])).
% 1.31/0.64  fof(f241,plain,(
% 1.31/0.64    spl5_21 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.31/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.31/0.64  fof(f277,plain,(
% 1.31/0.64    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl5_21),
% 1.31/0.64    inference(resolution,[],[f242,f41])).
% 1.31/0.64  fof(f41,plain,(
% 1.31/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.31/0.64    inference(cnf_transformation,[],[f19])).
% 1.31/0.64  fof(f19,plain,(
% 1.31/0.64    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.31/0.64    inference(ennf_transformation,[],[f8])).
% 1.31/0.64  fof(f8,axiom,(
% 1.31/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.31/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.31/0.64  fof(f242,plain,(
% 1.31/0.64    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_21),
% 1.31/0.64    inference(avatar_component_clause,[],[f241])).
% 1.31/0.64  fof(f284,plain,(
% 1.31/0.64    spl5_24 | ~spl5_21),
% 1.31/0.64    inference(avatar_split_clause,[],[f276,f241,f281])).
% 1.31/0.64  fof(f276,plain,(
% 1.31/0.64    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl5_21),
% 1.31/0.64    inference(resolution,[],[f242,f42])).
% 1.31/0.64  fof(f275,plain,(
% 1.31/0.64    spl5_21 | ~spl5_23),
% 1.31/0.64    inference(avatar_split_clause,[],[f273,f268,f241])).
% 1.31/0.64  fof(f268,plain,(
% 1.31/0.64    spl5_23 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.31/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.31/0.64  fof(f273,plain,(
% 1.31/0.64    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_23),
% 1.31/0.64    inference(resolution,[],[f270,f79])).
% 1.31/0.64  fof(f79,plain,(
% 1.31/0.64    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.31/0.64    inference(global_subsumption,[],[f36,f39])).
% 1.31/0.64  fof(f39,plain,(
% 1.31/0.64    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.31/0.64    inference(cnf_transformation,[],[f18])).
% 1.31/0.64  fof(f18,plain,(
% 1.31/0.64    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.31/0.64    inference(ennf_transformation,[],[f4])).
% 1.31/0.64  fof(f4,axiom,(
% 1.31/0.64    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.31/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.31/0.64  fof(f36,plain,(
% 1.31/0.64    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.31/0.64    inference(cnf_transformation,[],[f1])).
% 1.31/0.64  fof(f1,axiom,(
% 1.31/0.64    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.31/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.31/0.64  fof(f270,plain,(
% 1.31/0.64    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_23),
% 1.31/0.64    inference(avatar_component_clause,[],[f268])).
% 1.31/0.64  fof(f271,plain,(
% 1.31/0.64    spl5_23 | ~spl5_22),
% 1.31/0.64    inference(avatar_split_clause,[],[f266,f248,f268])).
% 1.31/0.64  fof(f248,plain,(
% 1.31/0.64    spl5_22 <=> r1_tarski(sK1,sK0)),
% 1.31/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.31/0.64  fof(f266,plain,(
% 1.31/0.64    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_22),
% 1.31/0.64    inference(resolution,[],[f250,f58])).
% 1.31/0.64  fof(f58,plain,(
% 1.31/0.64    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.31/0.64    inference(equality_resolution,[],[f46])).
% 1.31/0.64  fof(f46,plain,(
% 1.31/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.31/0.64    inference(cnf_transformation,[],[f3])).
% 1.31/0.64  fof(f3,axiom,(
% 1.31/0.64    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.31/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.31/0.64  fof(f250,plain,(
% 1.31/0.64    r1_tarski(sK1,sK0) | ~spl5_22),
% 1.31/0.64    inference(avatar_component_clause,[],[f248])).
% 1.31/0.64  fof(f260,plain,(
% 1.31/0.64    spl5_22 | ~spl5_3 | ~spl5_10),
% 1.31/0.64    inference(avatar_split_clause,[],[f257,f129,f70,f248])).
% 1.31/0.64  fof(f129,plain,(
% 1.31/0.64    spl5_10 <=> r1_tarski(sK2,sK0)),
% 1.31/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.31/0.64  fof(f257,plain,(
% 1.31/0.64    r1_tarski(sK1,sK0) | (~spl5_3 | ~spl5_10)),
% 1.31/0.64    inference(resolution,[],[f131,f122])).
% 1.31/0.64  fof(f131,plain,(
% 1.31/0.64    r1_tarski(sK2,sK0) | ~spl5_10),
% 1.31/0.64    inference(avatar_component_clause,[],[f129])).
% 1.31/0.64  fof(f256,plain,(
% 1.31/0.64    spl5_10 | ~spl5_8),
% 1.31/0.64    inference(avatar_split_clause,[],[f125,f109,f129])).
% 1.31/0.64  fof(f109,plain,(
% 1.31/0.64    spl5_8 <=> r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 1.31/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.31/0.64  fof(f125,plain,(
% 1.31/0.64    r1_tarski(sK2,sK0) | ~spl5_8),
% 1.31/0.64    inference(resolution,[],[f111,f57])).
% 1.31/0.64  fof(f57,plain,(
% 1.31/0.64    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.31/0.64    inference(equality_resolution,[],[f47])).
% 1.31/0.64  fof(f47,plain,(
% 1.31/0.64    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.31/0.64    inference(cnf_transformation,[],[f3])).
% 1.31/0.64  fof(f111,plain,(
% 1.31/0.64    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl5_8),
% 1.31/0.64    inference(avatar_component_clause,[],[f109])).
% 1.31/0.64  fof(f254,plain,(
% 1.31/0.64    ~spl5_7),
% 1.31/0.64    inference(avatar_contradiction_clause,[],[f252])).
% 1.31/0.64  fof(f252,plain,(
% 1.31/0.64    $false | ~spl5_7),
% 1.31/0.64    inference(resolution,[],[f107,f30])).
% 1.31/0.64  fof(f30,plain,(
% 1.31/0.64    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.31/0.64    inference(cnf_transformation,[],[f9])).
% 1.31/0.64  fof(f9,axiom,(
% 1.31/0.64    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.31/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.31/0.64  fof(f107,plain,(
% 1.31/0.64    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_7),
% 1.31/0.64    inference(avatar_component_clause,[],[f105])).
% 1.31/0.64  fof(f105,plain,(
% 1.31/0.64    spl5_7 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.31/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.31/0.64  fof(f244,plain,(
% 1.31/0.64    spl5_20 | ~spl5_21 | ~spl5_4 | ~spl5_2),
% 1.31/0.64    inference(avatar_split_clause,[],[f229,f65,f75,f241,f237])).
% 1.31/0.64  fof(f75,plain,(
% 1.31/0.64    spl5_4 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.31/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.31/0.64  fof(f65,plain,(
% 1.31/0.64    spl5_2 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.31/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.31/0.64  fof(f229,plain,(
% 1.31/0.64    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | r1_tarski(sK2,k3_subset_1(sK0,sK1)) | ~spl5_2),
% 1.31/0.64    inference(resolution,[],[f45,f67])).
% 1.31/0.64  fof(f67,plain,(
% 1.31/0.64    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~spl5_2),
% 1.31/0.64    inference(avatar_component_clause,[],[f65])).
% 1.31/0.64  fof(f45,plain,(
% 1.31/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X2,k3_subset_1(X0,X1))) )),
% 1.31/0.64    inference(cnf_transformation,[],[f23])).
% 1.31/0.64  fof(f23,plain,(
% 1.31/0.64    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.31/0.64    inference(flattening,[],[f22])).
% 1.31/0.64  fof(f22,plain,(
% 1.31/0.64    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.31/0.64    inference(ennf_transformation,[],[f12])).
% 1.31/0.64  fof(f12,axiom,(
% 1.31/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.31/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 1.31/0.64  fof(f112,plain,(
% 1.31/0.64    spl5_7 | spl5_8 | ~spl5_4),
% 1.31/0.64    inference(avatar_split_clause,[],[f100,f75,f109,f105])).
% 1.31/0.64  fof(f100,plain,(
% 1.31/0.64    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_4),
% 1.31/0.64    inference(resolution,[],[f40,f77])).
% 1.31/0.64  fof(f77,plain,(
% 1.31/0.64    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl5_4),
% 1.31/0.64    inference(avatar_component_clause,[],[f75])).
% 1.31/0.64  fof(f40,plain,(
% 1.31/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.31/0.64    inference(cnf_transformation,[],[f18])).
% 1.31/0.64  fof(f78,plain,(
% 1.31/0.64    spl5_4),
% 1.31/0.64    inference(avatar_split_clause,[],[f26,f75])).
% 1.31/0.64  fof(f26,plain,(
% 1.31/0.64    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.31/0.64    inference(cnf_transformation,[],[f17])).
% 1.31/0.64  fof(f17,plain,(
% 1.31/0.64    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.31/0.64    inference(flattening,[],[f16])).
% 1.31/0.64  fof(f16,plain,(
% 1.31/0.64    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.31/0.64    inference(ennf_transformation,[],[f15])).
% 1.31/0.64  fof(f15,negated_conjecture,(
% 1.31/0.64    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.31/0.64    inference(negated_conjecture,[],[f14])).
% 1.31/0.64  fof(f14,conjecture,(
% 1.31/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.31/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 1.31/0.64  fof(f73,plain,(
% 1.31/0.64    spl5_3),
% 1.31/0.64    inference(avatar_split_clause,[],[f27,f70])).
% 1.31/0.64  fof(f27,plain,(
% 1.31/0.64    r1_tarski(sK1,sK2)),
% 1.31/0.64    inference(cnf_transformation,[],[f17])).
% 1.31/0.64  fof(f68,plain,(
% 1.31/0.64    spl5_2),
% 1.31/0.64    inference(avatar_split_clause,[],[f28,f65])).
% 1.31/0.64  fof(f28,plain,(
% 1.31/0.64    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.31/0.64    inference(cnf_transformation,[],[f17])).
% 1.31/0.64  fof(f63,plain,(
% 1.31/0.64    ~spl5_1),
% 1.31/0.64    inference(avatar_split_clause,[],[f29,f60])).
% 1.31/0.64  fof(f29,plain,(
% 1.31/0.64    k1_xboole_0 != sK1),
% 1.31/0.64    inference(cnf_transformation,[],[f17])).
% 1.31/0.64  % SZS output end Proof for theBenchmark
% 1.31/0.64  % (25220)------------------------------
% 1.31/0.64  % (25220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.64  % (25220)Termination reason: Refutation
% 1.31/0.64  
% 1.31/0.64  % (25220)Memory used [KB]: 11001
% 1.31/0.64  % (25220)Time elapsed: 0.197 s
% 1.31/0.64  % (25220)------------------------------
% 1.31/0.64  % (25220)------------------------------
% 1.31/0.64  % (25210)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 2.04/0.64  % (25198)Success in time 0.268 s
%------------------------------------------------------------------------------
