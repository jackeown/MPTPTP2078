%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:44 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 228 expanded)
%              Number of leaves         :   25 (  96 expanded)
%              Depth                    :   10
%              Number of atoms          :  267 ( 498 expanded)
%              Number of equality atoms :   62 ( 152 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2807,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f53,f58,f77,f129,f177,f185,f192,f387,f395,f421,f784,f804,f810,f866,f2773])).

fof(f2773,plain,
    ( ~ spl3_34
    | spl3_9
    | ~ spl3_30
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f2772,f841,f384,f126,f418])).

fof(f418,plain,
    ( spl3_34
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f126,plain,
    ( spl3_9
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f384,plain,
    ( spl3_30
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f841,plain,
    ( spl3_50
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f2772,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl3_9
    | ~ spl3_30
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f2718,f843])).

fof(f843,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f841])).

fof(f2718,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl3_9
    | ~ spl3_30 ),
    inference(backward_demodulation,[],[f127,f406])).

fof(f406,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_30 ),
    inference(superposition,[],[f35,f386])).

fof(f386,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f384])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f127,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f866,plain,
    ( spl3_50
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f865,f121,f55,f841])).

fof(f55,plain,
    ( spl3_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f121,plain,
    ( spl3_8
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f865,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_8 ),
    inference(duplicate_literal_removal,[],[f864])).

fof(f864,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f863,f79])).

fof(f79,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f863,plain,
    ( ~ v1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f834,f35])).

fof(f834,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),sK0))
    | sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f107,f123])).

fof(f123,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_xboole_0(X0,X1))
      | ~ v1_xboole_0(k4_xboole_0(X1,X0))
      | X0 = X1 ) ),
    inference(extensionality_resolution,[],[f34,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f810,plain,
    ( spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f808,f49,f121])).

fof(f49,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f808,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f51,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f33,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f51,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f804,plain,
    ( spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f236,f126,f40])).

fof(f40,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f236,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_9 ),
    inference(trivial_inequality_removal,[],[f230])).

fof(f230,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_9 ),
    inference(superposition,[],[f38,f128])).

fof(f128,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f784,plain,
    ( spl3_3
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f783,f392,f384,f49])).

fof(f392,plain,
    ( spl3_31
  <=> sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f783,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f782,f386])).

fof(f782,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_31 ),
    inference(trivial_inequality_removal,[],[f781])).

fof(f781,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f745,f79])).

fof(f745,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))
    | r1_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_31 ),
    inference(superposition,[],[f162,f394])).

fof(f394,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f392])).

fof(f162,plain,(
    ! [X17,X15,X16] :
      ( k1_xboole_0 != k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X15,k2_xboole_0(X16,X17))))
      | r1_xboole_0(k4_xboole_0(X15,X16),X17) ) ),
    inference(forward_demodulation,[],[f156,f35])).

fof(f156,plain,(
    ! [X17,X15,X16] :
      ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(X15,X16),k4_xboole_0(X15,k2_xboole_0(X16,X17)))
      | r1_xboole_0(k4_xboole_0(X15,X16),X17) ) ),
    inference(superposition,[],[f38,f35])).

fof(f421,plain,
    ( spl3_34
    | ~ spl3_13
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f405,f384,f189,f418])).

fof(f189,plain,
    ( spl3_13
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f405,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_13
    | ~ spl3_30 ),
    inference(backward_demodulation,[],[f191,f386])).

fof(f191,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f189])).

fof(f395,plain,
    ( spl3_31
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f390,f126,f55,f392])).

fof(f390,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_9 ),
    inference(duplicate_literal_removal,[],[f389])).

fof(f389,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f388,f79])).

fof(f388,plain,
    ( ~ v1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f342,f35])).

fof(f342,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK0))
    | sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_9 ),
    inference(superposition,[],[f107,f128])).

fof(f387,plain,
    ( spl3_30
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f382,f189,f55,f384])).

fof(f382,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_13 ),
    inference(duplicate_literal_removal,[],[f381])).

fof(f381,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f380,f79])).

fof(f380,plain,
    ( ~ v1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f341,f35])).

fof(f341,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))
    | sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_13 ),
    inference(superposition,[],[f107,f191])).

fof(f192,plain,
    ( spl3_13
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f186,f44,f189])).

fof(f44,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f186,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f46,f37])).

fof(f46,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f185,plain,
    ( spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f179,f62,f44])).

fof(f62,plain,
    ( spl3_5
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f179,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(resolution,[],[f64,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f64,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f177,plain,
    ( spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f173,f74,f62])).

fof(f74,plain,
    ( spl3_7
  <=> r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f173,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f97,f76])).

fof(f76,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X1),X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(resolution,[],[f36,f25])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f129,plain,
    ( spl3_9
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f117,f40,f126])).

fof(f117,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_1 ),
    inference(resolution,[],[f37,f42])).

fof(f42,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f77,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f72,f40,f74])).

fof(f72,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f42,f30])).

fof(f58,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f55])).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f53,plain,
    ( ~ spl3_3
    | ~ spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f40,f44,f49])).

fof(f21,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f52,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f22,f49,f40])).

fof(f22,plain,
    ( r1_xboole_0(sK0,sK2)
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f23,f44,f40])).

fof(f23,plain,
    ( r1_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:43:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (819691521)
% 0.14/0.38  ipcrm: permission denied for id (819724290)
% 0.14/0.38  ipcrm: permission denied for id (819789829)
% 0.14/0.38  ipcrm: permission denied for id (819822598)
% 0.14/0.38  ipcrm: permission denied for id (819855368)
% 0.14/0.39  ipcrm: permission denied for id (819888138)
% 0.14/0.39  ipcrm: permission denied for id (819920907)
% 0.14/0.39  ipcrm: permission denied for id (819986445)
% 0.14/0.39  ipcrm: permission denied for id (820019214)
% 0.14/0.39  ipcrm: permission denied for id (820084752)
% 0.14/0.40  ipcrm: permission denied for id (820150292)
% 0.14/0.40  ipcrm: permission denied for id (820183061)
% 0.21/0.40  ipcrm: permission denied for id (820215831)
% 0.21/0.40  ipcrm: permission denied for id (820248600)
% 0.21/0.40  ipcrm: permission denied for id (820281369)
% 0.21/0.41  ipcrm: permission denied for id (820346907)
% 0.21/0.41  ipcrm: permission denied for id (820412445)
% 0.21/0.41  ipcrm: permission denied for id (820510752)
% 0.21/0.41  ipcrm: permission denied for id (820543521)
% 0.21/0.42  ipcrm: permission denied for id (820609059)
% 0.21/0.42  ipcrm: permission denied for id (820641828)
% 0.21/0.42  ipcrm: permission denied for id (820707366)
% 0.21/0.42  ipcrm: permission denied for id (820772904)
% 0.21/0.42  ipcrm: permission denied for id (820805673)
% 0.21/0.43  ipcrm: permission denied for id (820871212)
% 0.21/0.43  ipcrm: permission denied for id (820936750)
% 0.21/0.43  ipcrm: permission denied for id (821002288)
% 0.21/0.43  ipcrm: permission denied for id (821035058)
% 0.21/0.43  ipcrm: permission denied for id (821067827)
% 0.21/0.44  ipcrm: permission denied for id (821133364)
% 0.21/0.44  ipcrm: permission denied for id (821166133)
% 0.21/0.44  ipcrm: permission denied for id (821231671)
% 0.21/0.44  ipcrm: permission denied for id (821264440)
% 0.21/0.44  ipcrm: permission denied for id (821297209)
% 0.21/0.44  ipcrm: permission denied for id (821329978)
% 0.21/0.45  ipcrm: permission denied for id (821395516)
% 0.21/0.45  ipcrm: permission denied for id (821624899)
% 0.21/0.46  ipcrm: permission denied for id (821657668)
% 0.21/0.46  ipcrm: permission denied for id (821690438)
% 0.21/0.46  ipcrm: permission denied for id (821755976)
% 0.21/0.46  ipcrm: permission denied for id (821788745)
% 0.21/0.46  ipcrm: permission denied for id (821821514)
% 0.21/0.47  ipcrm: permission denied for id (821952592)
% 0.21/0.47  ipcrm: permission denied for id (821985361)
% 0.21/0.47  ipcrm: permission denied for id (822018130)
% 0.21/0.48  ipcrm: permission denied for id (822149207)
% 0.21/0.48  ipcrm: permission denied for id (822214744)
% 0.21/0.48  ipcrm: permission denied for id (822247513)
% 0.21/0.48  ipcrm: permission denied for id (822280282)
% 0.21/0.49  ipcrm: permission denied for id (822313052)
% 0.21/0.49  ipcrm: permission denied for id (822345821)
% 0.21/0.49  ipcrm: permission denied for id (822542435)
% 0.21/0.50  ipcrm: permission denied for id (822607973)
% 0.21/0.50  ipcrm: permission denied for id (822640742)
% 0.21/0.50  ipcrm: permission denied for id (822673512)
% 0.21/0.50  ipcrm: permission denied for id (822771820)
% 0.21/0.51  ipcrm: permission denied for id (822837358)
% 0.21/0.51  ipcrm: permission denied for id (822870128)
% 0.21/0.51  ipcrm: permission denied for id (822902897)
% 0.21/0.51  ipcrm: permission denied for id (822935667)
% 0.21/0.52  ipcrm: permission denied for id (823001205)
% 0.21/0.52  ipcrm: permission denied for id (823066743)
% 0.21/0.52  ipcrm: permission denied for id (823132281)
% 0.21/0.53  ipcrm: permission denied for id (823296127)
% 1.01/0.65  % (21376)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.01/0.66  % (21392)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.01/0.67  % (21384)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.01/0.67  % (21386)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.01/0.67  % (21400)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.01/0.68  % (21394)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.01/0.68  % (21392)Refutation not found, incomplete strategy% (21392)------------------------------
% 1.01/0.68  % (21392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.01/0.68  % (21392)Termination reason: Refutation not found, incomplete strategy
% 1.01/0.68  
% 1.01/0.68  % (21392)Memory used [KB]: 10618
% 1.01/0.68  % (21392)Time elapsed: 0.119 s
% 1.01/0.68  % (21392)------------------------------
% 1.01/0.68  % (21392)------------------------------
% 1.01/0.68  % (21386)Refutation not found, incomplete strategy% (21386)------------------------------
% 1.01/0.68  % (21386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.01/0.68  % (21384)Refutation not found, incomplete strategy% (21384)------------------------------
% 1.01/0.68  % (21384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.01/0.68  % (21384)Termination reason: Refutation not found, incomplete strategy
% 1.01/0.68  
% 1.01/0.68  % (21384)Memory used [KB]: 10618
% 1.01/0.68  % (21384)Time elapsed: 0.120 s
% 1.01/0.68  % (21384)------------------------------
% 1.01/0.68  % (21384)------------------------------
% 1.01/0.69  % (21386)Termination reason: Refutation not found, incomplete strategy
% 1.01/0.69  
% 1.01/0.69  % (21386)Memory used [KB]: 10618
% 1.01/0.69  % (21386)Time elapsed: 0.101 s
% 1.01/0.69  % (21386)------------------------------
% 1.01/0.69  % (21386)------------------------------
% 1.01/0.69  % (21402)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.01/0.70  % (21382)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.01/0.70  % (21390)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.01/0.70  % (21387)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.01/0.70  % (21379)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.01/0.70  % (21375)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.01/0.70  % (21395)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.01/0.70  % (21375)Refutation not found, incomplete strategy% (21375)------------------------------
% 1.01/0.70  % (21375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.01/0.70  % (21375)Termination reason: Refutation not found, incomplete strategy
% 1.01/0.70  
% 1.01/0.70  % (21375)Memory used [KB]: 1663
% 1.01/0.70  % (21375)Time elapsed: 0.124 s
% 1.01/0.70  % (21375)------------------------------
% 1.01/0.70  % (21375)------------------------------
% 1.01/0.71  % (21378)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.01/0.71  % (21399)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.01/0.71  % (21391)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.01/0.71  % (21404)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.01/0.71  % (21403)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.01/0.71  % (21377)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.01/0.71  % (21396)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.01/0.72  % (21398)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.01/0.72  % (21385)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.62/0.72  % (21388)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.62/0.72  % (21389)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.62/0.72  % (21383)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.62/0.73  % (21397)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.62/0.73  % (21393)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.62/0.73  % (21397)Refutation not found, incomplete strategy% (21397)------------------------------
% 1.62/0.73  % (21397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.73  % (21397)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.73  
% 1.62/0.73  % (21397)Memory used [KB]: 10618
% 1.62/0.73  % (21397)Time elapsed: 0.157 s
% 1.62/0.73  % (21397)------------------------------
% 1.62/0.73  % (21397)------------------------------
% 1.62/0.73  % (21380)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.62/0.73  % (21385)Refutation not found, incomplete strategy% (21385)------------------------------
% 1.62/0.73  % (21385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.73  % (21385)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.73  
% 1.62/0.73  % (21385)Memory used [KB]: 10618
% 1.62/0.73  % (21385)Time elapsed: 0.160 s
% 1.62/0.73  % (21385)------------------------------
% 1.62/0.73  % (21385)------------------------------
% 1.62/0.73  % (21381)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.62/0.74  % (21401)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.04/0.79  % (21406)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.04/0.84  % (21405)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.04/0.84  % (21407)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.04/0.85  % (21391)Refutation found. Thanks to Tanya!
% 2.04/0.85  % SZS status Theorem for theBenchmark
% 2.50/0.86  % (21405)Refutation not found, incomplete strategy% (21405)------------------------------
% 2.50/0.86  % (21405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.50/0.86  % (21405)Termination reason: Refutation not found, incomplete strategy
% 2.50/0.86  
% 2.50/0.86  % (21405)Memory used [KB]: 6140
% 2.50/0.86  % (21405)Time elapsed: 0.143 s
% 2.50/0.86  % (21405)------------------------------
% 2.50/0.86  % (21405)------------------------------
% 2.50/0.87  % SZS output start Proof for theBenchmark
% 2.50/0.87  fof(f2807,plain,(
% 2.50/0.87    $false),
% 2.50/0.87    inference(avatar_sat_refutation,[],[f47,f52,f53,f58,f77,f129,f177,f185,f192,f387,f395,f421,f784,f804,f810,f866,f2773])).
% 2.50/0.87  fof(f2773,plain,(
% 2.50/0.87    ~spl3_34 | spl3_9 | ~spl3_30 | ~spl3_50),
% 2.50/0.87    inference(avatar_split_clause,[],[f2772,f841,f384,f126,f418])).
% 2.50/0.87  fof(f418,plain,(
% 2.50/0.87    spl3_34 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 2.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 2.50/0.87  fof(f126,plain,(
% 2.50/0.87    spl3_9 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 2.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.50/0.87  fof(f384,plain,(
% 2.50/0.87    spl3_30 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 2.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 2.50/0.87  fof(f841,plain,(
% 2.50/0.87    spl3_50 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 2.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 2.50/0.87  fof(f2772,plain,(
% 2.50/0.87    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (spl3_9 | ~spl3_30 | ~spl3_50)),
% 2.50/0.87    inference(forward_demodulation,[],[f2718,f843])).
% 2.50/0.87  fof(f843,plain,(
% 2.50/0.87    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_50),
% 2.50/0.87    inference(avatar_component_clause,[],[f841])).
% 2.50/0.87  fof(f2718,plain,(
% 2.50/0.87    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (spl3_9 | ~spl3_30)),
% 2.50/0.87    inference(backward_demodulation,[],[f127,f406])).
% 2.50/0.87  fof(f406,plain,(
% 2.50/0.87    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)) ) | ~spl3_30),
% 2.50/0.87    inference(superposition,[],[f35,f386])).
% 2.50/0.87  fof(f386,plain,(
% 2.50/0.87    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_30),
% 2.50/0.87    inference(avatar_component_clause,[],[f384])).
% 2.50/0.87  fof(f35,plain,(
% 2.50/0.87    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.50/0.87    inference(cnf_transformation,[],[f7])).
% 2.50/0.87  fof(f7,axiom,(
% 2.50/0.87    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.50/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.50/0.87  fof(f127,plain,(
% 2.50/0.87    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | spl3_9),
% 2.50/0.87    inference(avatar_component_clause,[],[f126])).
% 2.50/0.87  fof(f866,plain,(
% 2.50/0.87    spl3_50 | ~spl3_4 | ~spl3_8),
% 2.50/0.87    inference(avatar_split_clause,[],[f865,f121,f55,f841])).
% 2.50/0.87  fof(f55,plain,(
% 2.50/0.87    spl3_4 <=> v1_xboole_0(k1_xboole_0)),
% 2.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.50/0.87  fof(f121,plain,(
% 2.50/0.87    spl3_8 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.50/0.87  fof(f865,plain,(
% 2.50/0.87    ~v1_xboole_0(k1_xboole_0) | sK0 = k4_xboole_0(sK0,sK2) | ~spl3_8),
% 2.50/0.87    inference(duplicate_literal_removal,[],[f864])).
% 2.50/0.87  fof(f864,plain,(
% 2.50/0.87    ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | sK0 = k4_xboole_0(sK0,sK2) | ~spl3_8),
% 2.50/0.87    inference(forward_demodulation,[],[f863,f79])).
% 2.50/0.87  fof(f79,plain,(
% 2.50/0.87    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 2.50/0.87    inference(superposition,[],[f26,f27])).
% 2.50/0.87  fof(f27,plain,(
% 2.50/0.87    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.50/0.87    inference(cnf_transformation,[],[f1])).
% 2.50/0.87  fof(f1,axiom,(
% 2.50/0.87    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.50/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.50/0.87  fof(f26,plain,(
% 2.50/0.87    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.50/0.87    inference(cnf_transformation,[],[f8])).
% 2.50/0.87  fof(f8,axiom,(
% 2.50/0.87    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.50/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.50/0.87  fof(f863,plain,(
% 2.50/0.87    ~v1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK2,sK0))) | ~v1_xboole_0(k1_xboole_0) | sK0 = k4_xboole_0(sK0,sK2) | ~spl3_8),
% 2.50/0.87    inference(forward_demodulation,[],[f834,f35])).
% 2.50/0.87  fof(f834,plain,(
% 2.50/0.87    ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)) | sK0 = k4_xboole_0(sK0,sK2) | ~spl3_8),
% 2.50/0.87    inference(superposition,[],[f107,f123])).
% 2.50/0.87  fof(f123,plain,(
% 2.50/0.87    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_8),
% 2.50/0.87    inference(avatar_component_clause,[],[f121])).
% 2.50/0.87  fof(f107,plain,(
% 2.50/0.87    ( ! [X0,X1] : (~v1_xboole_0(k4_xboole_0(X0,X1)) | ~v1_xboole_0(k4_xboole_0(X1,X0)) | X0 = X1) )),
% 2.50/0.87    inference(extensionality_resolution,[],[f34,f31])).
% 2.50/0.87  fof(f31,plain,(
% 2.50/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 2.50/0.87    inference(cnf_transformation,[],[f17])).
% 2.50/0.87  fof(f17,plain,(
% 2.50/0.87    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 2.50/0.87    inference(ennf_transformation,[],[f5])).
% 2.50/0.87  fof(f5,axiom,(
% 2.50/0.87    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 2.50/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).
% 2.50/0.87  fof(f34,plain,(
% 2.50/0.87    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 2.50/0.87    inference(cnf_transformation,[],[f18])).
% 2.50/0.87  fof(f18,plain,(
% 2.50/0.87    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.50/0.87    inference(ennf_transformation,[],[f12])).
% 2.50/0.87  fof(f12,axiom,(
% 2.50/0.87    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.50/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 2.50/0.87  fof(f810,plain,(
% 2.50/0.87    spl3_8 | ~spl3_3),
% 2.50/0.87    inference(avatar_split_clause,[],[f808,f49,f121])).
% 2.50/0.87  fof(f49,plain,(
% 2.50/0.87    spl3_3 <=> r1_xboole_0(sK0,sK2)),
% 2.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.50/0.87  fof(f808,plain,(
% 2.50/0.87    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_3),
% 2.50/0.87    inference(resolution,[],[f51,f37])).
% 2.50/0.87  fof(f37,plain,(
% 2.50/0.87    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.50/0.87    inference(definition_unfolding,[],[f33,f28])).
% 2.50/0.87  fof(f28,plain,(
% 2.50/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.50/0.87    inference(cnf_transformation,[],[f9])).
% 2.50/0.87  fof(f9,axiom,(
% 2.50/0.87    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.50/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.50/0.87  fof(f33,plain,(
% 2.50/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.50/0.87    inference(cnf_transformation,[],[f2])).
% 2.50/0.87  fof(f2,axiom,(
% 2.50/0.87    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.50/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.50/0.87  fof(f51,plain,(
% 2.50/0.87    r1_xboole_0(sK0,sK2) | ~spl3_3),
% 2.50/0.87    inference(avatar_component_clause,[],[f49])).
% 2.50/0.87  fof(f804,plain,(
% 2.50/0.87    spl3_1 | ~spl3_9),
% 2.50/0.87    inference(avatar_split_clause,[],[f236,f126,f40])).
% 2.50/0.87  fof(f40,plain,(
% 2.50/0.87    spl3_1 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.50/0.87  fof(f236,plain,(
% 2.50/0.87    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_9),
% 2.50/0.87    inference(trivial_inequality_removal,[],[f230])).
% 2.50/0.87  fof(f230,plain,(
% 2.50/0.87    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_9),
% 2.50/0.87    inference(superposition,[],[f38,f128])).
% 2.50/0.87  fof(f128,plain,(
% 2.50/0.87    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | ~spl3_9),
% 2.50/0.87    inference(avatar_component_clause,[],[f126])).
% 2.50/0.87  fof(f38,plain,(
% 2.50/0.87    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.50/0.87    inference(definition_unfolding,[],[f32,f28])).
% 2.50/0.87  fof(f32,plain,(
% 2.50/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.50/0.87    inference(cnf_transformation,[],[f2])).
% 2.50/0.87  fof(f784,plain,(
% 2.50/0.87    spl3_3 | ~spl3_30 | ~spl3_31),
% 2.50/0.87    inference(avatar_split_clause,[],[f783,f392,f384,f49])).
% 2.50/0.87  fof(f392,plain,(
% 2.50/0.87    spl3_31 <=> sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.50/0.87  fof(f783,plain,(
% 2.50/0.87    r1_xboole_0(sK0,sK2) | (~spl3_30 | ~spl3_31)),
% 2.50/0.87    inference(forward_demodulation,[],[f782,f386])).
% 2.50/0.87  fof(f782,plain,(
% 2.50/0.87    r1_xboole_0(k4_xboole_0(sK0,sK1),sK2) | ~spl3_31),
% 2.50/0.87    inference(trivial_inequality_removal,[],[f781])).
% 2.50/0.87  fof(f781,plain,(
% 2.50/0.87    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k4_xboole_0(sK0,sK1),sK2) | ~spl3_31),
% 2.50/0.87    inference(forward_demodulation,[],[f745,f79])).
% 2.50/0.87  fof(f745,plain,(
% 2.50/0.87    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) | r1_xboole_0(k4_xboole_0(sK0,sK1),sK2) | ~spl3_31),
% 2.50/0.87    inference(superposition,[],[f162,f394])).
% 2.50/0.87  fof(f394,plain,(
% 2.50/0.87    sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_31),
% 2.50/0.87    inference(avatar_component_clause,[],[f392])).
% 2.50/0.87  fof(f162,plain,(
% 2.50/0.87    ( ! [X17,X15,X16] : (k1_xboole_0 != k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X15,k2_xboole_0(X16,X17)))) | r1_xboole_0(k4_xboole_0(X15,X16),X17)) )),
% 2.50/0.87    inference(forward_demodulation,[],[f156,f35])).
% 2.50/0.87  fof(f156,plain,(
% 2.50/0.87    ( ! [X17,X15,X16] : (k1_xboole_0 != k4_xboole_0(k4_xboole_0(X15,X16),k4_xboole_0(X15,k2_xboole_0(X16,X17))) | r1_xboole_0(k4_xboole_0(X15,X16),X17)) )),
% 2.50/0.87    inference(superposition,[],[f38,f35])).
% 2.50/0.87  fof(f421,plain,(
% 2.50/0.87    spl3_34 | ~spl3_13 | ~spl3_30),
% 2.50/0.87    inference(avatar_split_clause,[],[f405,f384,f189,f418])).
% 2.50/0.87  fof(f189,plain,(
% 2.50/0.87    spl3_13 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.50/0.87  fof(f405,plain,(
% 2.50/0.87    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl3_13 | ~spl3_30)),
% 2.50/0.87    inference(backward_demodulation,[],[f191,f386])).
% 2.50/0.87  fof(f191,plain,(
% 2.50/0.87    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_13),
% 2.50/0.87    inference(avatar_component_clause,[],[f189])).
% 2.50/0.87  fof(f395,plain,(
% 2.50/0.87    spl3_31 | ~spl3_4 | ~spl3_9),
% 2.50/0.87    inference(avatar_split_clause,[],[f390,f126,f55,f392])).
% 2.50/0.87  fof(f390,plain,(
% 2.50/0.87    ~v1_xboole_0(k1_xboole_0) | sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_9),
% 2.50/0.87    inference(duplicate_literal_removal,[],[f389])).
% 2.50/0.87  fof(f389,plain,(
% 2.50/0.87    ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_9),
% 2.50/0.87    inference(forward_demodulation,[],[f388,f79])).
% 2.50/0.87  fof(f388,plain,(
% 2.50/0.87    ~v1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK0))) | ~v1_xboole_0(k1_xboole_0) | sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_9),
% 2.50/0.87    inference(forward_demodulation,[],[f342,f35])).
% 2.50/0.87  fof(f342,plain,(
% 2.50/0.87    ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK0)) | sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_9),
% 2.50/0.87    inference(superposition,[],[f107,f128])).
% 2.50/0.87  fof(f387,plain,(
% 2.50/0.87    spl3_30 | ~spl3_4 | ~spl3_13),
% 2.50/0.87    inference(avatar_split_clause,[],[f382,f189,f55,f384])).
% 2.50/0.87  fof(f382,plain,(
% 2.50/0.87    ~v1_xboole_0(k1_xboole_0) | sK0 = k4_xboole_0(sK0,sK1) | ~spl3_13),
% 2.50/0.87    inference(duplicate_literal_removal,[],[f381])).
% 2.50/0.87  fof(f381,plain,(
% 2.50/0.87    ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | sK0 = k4_xboole_0(sK0,sK1) | ~spl3_13),
% 2.50/0.87    inference(forward_demodulation,[],[f380,f79])).
% 2.50/0.87  fof(f380,plain,(
% 2.50/0.87    ~v1_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))) | ~v1_xboole_0(k1_xboole_0) | sK0 = k4_xboole_0(sK0,sK1) | ~spl3_13),
% 2.50/0.87    inference(forward_demodulation,[],[f341,f35])).
% 2.50/0.87  fof(f341,plain,(
% 2.50/0.87    ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) | sK0 = k4_xboole_0(sK0,sK1) | ~spl3_13),
% 2.50/0.87    inference(superposition,[],[f107,f191])).
% 2.50/0.87  fof(f192,plain,(
% 2.50/0.87    spl3_13 | ~spl3_2),
% 2.50/0.87    inference(avatar_split_clause,[],[f186,f44,f189])).
% 2.50/0.87  fof(f44,plain,(
% 2.50/0.87    spl3_2 <=> r1_xboole_0(sK0,sK1)),
% 2.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.50/0.87  fof(f186,plain,(
% 2.50/0.87    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_2),
% 2.50/0.87    inference(resolution,[],[f46,f37])).
% 2.50/0.87  fof(f46,plain,(
% 2.50/0.87    r1_xboole_0(sK0,sK1) | ~spl3_2),
% 2.50/0.87    inference(avatar_component_clause,[],[f44])).
% 2.50/0.87  fof(f185,plain,(
% 2.50/0.87    spl3_2 | ~spl3_5),
% 2.50/0.87    inference(avatar_split_clause,[],[f179,f62,f44])).
% 2.50/0.87  fof(f62,plain,(
% 2.50/0.87    spl3_5 <=> r1_xboole_0(sK1,sK0)),
% 2.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.50/0.87  fof(f179,plain,(
% 2.50/0.87    r1_xboole_0(sK0,sK1) | ~spl3_5),
% 2.50/0.87    inference(resolution,[],[f64,f30])).
% 2.50/0.87  fof(f30,plain,(
% 2.50/0.87    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.50/0.87    inference(cnf_transformation,[],[f16])).
% 2.50/0.87  fof(f16,plain,(
% 2.50/0.87    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.50/0.87    inference(ennf_transformation,[],[f4])).
% 2.50/0.87  fof(f4,axiom,(
% 2.50/0.87    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.50/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.50/0.87  fof(f64,plain,(
% 2.50/0.87    r1_xboole_0(sK1,sK0) | ~spl3_5),
% 2.50/0.87    inference(avatar_component_clause,[],[f62])).
% 2.50/0.87  fof(f177,plain,(
% 2.50/0.87    spl3_5 | ~spl3_7),
% 2.50/0.87    inference(avatar_split_clause,[],[f173,f74,f62])).
% 2.50/0.87  fof(f74,plain,(
% 2.50/0.87    spl3_7 <=> r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)),
% 2.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.50/0.87  fof(f173,plain,(
% 2.50/0.87    r1_xboole_0(sK1,sK0) | ~spl3_7),
% 2.50/0.87    inference(resolution,[],[f97,f76])).
% 2.50/0.87  fof(f76,plain,(
% 2.50/0.87    r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) | ~spl3_7),
% 2.50/0.87    inference(avatar_component_clause,[],[f74])).
% 2.50/0.87  fof(f97,plain,(
% 2.50/0.87    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_xboole_0(X0,X1),X2) | r1_xboole_0(X0,X2)) )),
% 2.50/0.87    inference(resolution,[],[f36,f25])).
% 2.50/0.87  fof(f25,plain,(
% 2.50/0.87    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.50/0.87    inference(cnf_transformation,[],[f11])).
% 2.50/0.87  fof(f11,axiom,(
% 2.50/0.87    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.50/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.50/0.87  fof(f36,plain,(
% 2.50/0.87    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 2.50/0.87    inference(cnf_transformation,[],[f20])).
% 2.50/0.87  fof(f20,plain,(
% 2.50/0.87    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.50/0.87    inference(flattening,[],[f19])).
% 2.50/0.87  fof(f19,plain,(
% 2.50/0.87    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.50/0.87    inference(ennf_transformation,[],[f10])).
% 2.50/0.87  fof(f10,axiom,(
% 2.50/0.87    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.50/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.50/0.87  fof(f129,plain,(
% 2.50/0.87    spl3_9 | ~spl3_1),
% 2.50/0.87    inference(avatar_split_clause,[],[f117,f40,f126])).
% 2.50/0.87  fof(f117,plain,(
% 2.50/0.87    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | ~spl3_1),
% 2.50/0.87    inference(resolution,[],[f37,f42])).
% 2.50/0.87  fof(f42,plain,(
% 2.50/0.87    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_1),
% 2.50/0.87    inference(avatar_component_clause,[],[f40])).
% 2.50/0.87  fof(f77,plain,(
% 2.50/0.87    spl3_7 | ~spl3_1),
% 2.50/0.87    inference(avatar_split_clause,[],[f72,f40,f74])).
% 2.50/0.87  fof(f72,plain,(
% 2.50/0.87    r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) | ~spl3_1),
% 2.50/0.87    inference(resolution,[],[f42,f30])).
% 2.50/0.87  fof(f58,plain,(
% 2.50/0.87    spl3_4),
% 2.50/0.87    inference(avatar_split_clause,[],[f24,f55])).
% 2.50/0.87  fof(f24,plain,(
% 2.50/0.87    v1_xboole_0(k1_xboole_0)),
% 2.50/0.87    inference(cnf_transformation,[],[f3])).
% 2.50/0.87  fof(f3,axiom,(
% 2.50/0.87    v1_xboole_0(k1_xboole_0)),
% 2.50/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.50/0.87  fof(f53,plain,(
% 2.50/0.87    ~spl3_3 | ~spl3_2 | ~spl3_1),
% 2.50/0.87    inference(avatar_split_clause,[],[f21,f40,f44,f49])).
% 2.50/0.87  fof(f21,plain,(
% 2.50/0.87    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK2)),
% 2.50/0.87    inference(cnf_transformation,[],[f15])).
% 2.50/0.87  fof(f15,plain,(
% 2.50/0.87    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.50/0.87    inference(ennf_transformation,[],[f14])).
% 2.50/0.87  fof(f14,negated_conjecture,(
% 2.50/0.87    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.50/0.87    inference(negated_conjecture,[],[f13])).
% 2.50/0.87  fof(f13,conjecture,(
% 2.50/0.87    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.50/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.50/0.87  fof(f52,plain,(
% 2.50/0.87    spl3_1 | spl3_3),
% 2.50/0.87    inference(avatar_split_clause,[],[f22,f49,f40])).
% 2.50/0.87  fof(f22,plain,(
% 2.50/0.87    r1_xboole_0(sK0,sK2) | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.50/0.87    inference(cnf_transformation,[],[f15])).
% 2.50/0.87  fof(f47,plain,(
% 2.50/0.87    spl3_1 | spl3_2),
% 2.50/0.87    inference(avatar_split_clause,[],[f23,f44,f40])).
% 2.50/0.87  fof(f23,plain,(
% 2.50/0.87    r1_xboole_0(sK0,sK1) | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.50/0.87    inference(cnf_transformation,[],[f15])).
% 2.50/0.87  % SZS output end Proof for theBenchmark
% 2.50/0.87  % (21391)------------------------------
% 2.50/0.87  % (21391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.50/0.87  % (21391)Termination reason: Refutation
% 2.50/0.87  
% 2.50/0.87  % (21391)Memory used [KB]: 12920
% 2.50/0.87  % (21391)Time elapsed: 0.279 s
% 2.50/0.87  % (21391)------------------------------
% 2.50/0.87  % (21391)------------------------------
% 2.50/0.87  % (21241)Success in time 0.498 s
%------------------------------------------------------------------------------
