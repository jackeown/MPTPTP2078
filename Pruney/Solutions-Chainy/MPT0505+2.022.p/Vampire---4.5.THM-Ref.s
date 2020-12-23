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
% DateTime   : Thu Dec  3 12:48:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 179 expanded)
%              Number of leaves         :   24 (  77 expanded)
%              Depth                    :    7
%              Number of atoms          :  186 ( 347 expanded)
%              Number of equality atoms :   74 ( 153 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f60,f66,f73,f86,f97,f110,f118,f137,f140,f146])).

fof(f146,plain,
    ( spl3_12
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f141,f115,f94,f143])).

fof(f143,plain,
    ( spl3_12
  <=> k3_xboole_0(sK1,sK0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),sK1),k3_xboole_0(k4_xboole_0(sK1,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f94,plain,
    ( spl3_8
  <=> sK1 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f115,plain,
    ( spl3_10
  <=> k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f141,plain,
    ( k3_xboole_0(sK1,sK0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),sK1),k3_xboole_0(k4_xboole_0(sK1,sK0),sK1))
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f127,f117])).

fof(f117,plain,
    ( k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f127,plain,
    ( k3_xboole_0(sK1,sK0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK1,sK0)),sK1),k3_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK1,sK0)),sK1))
    | ~ spl3_8 ),
    inference(superposition,[],[f36,f96])).

fof(f96,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k2_xboole_0(X0,X1)),k3_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f28,f28])).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f140,plain,
    ( spl3_11
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f139,f63,f57,f134])).

fof(f134,plain,
    ( spl3_11
  <=> sK0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),sK1),k3_xboole_0(k4_xboole_0(sK1,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f57,plain,
    ( spl3_4
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f63,plain,
    ( spl3_5
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f139,plain,
    ( sK0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),sK1),k3_xboole_0(k4_xboole_0(sK1,sK0),sK1))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f126,f59])).

fof(f59,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f126,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)),sK1))
    | ~ spl3_5 ),
    inference(superposition,[],[f36,f65])).

fof(f65,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f137,plain,
    ( spl3_11
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f132,f63,f57,f134])).

fof(f132,plain,
    ( sK0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),sK1),k3_xboole_0(k4_xboole_0(sK1,sK0),sK1))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f119,f65])).

fof(f119,plain,
    ( sK0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),sK0),k2_xboole_0(sK0,sK1)),k3_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),sK0),k2_xboole_0(sK0,sK1)))
    | ~ spl3_4 ),
    inference(superposition,[],[f36,f59])).

fof(f118,plain,
    ( spl3_10
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f113,f94,f70,f115])).

fof(f70,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f113,plain,
    ( k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK0))
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f112,f96])).

fof(f112,plain,
    ( k4_xboole_0(sK1,sK0) = k4_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f102,f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f102,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0)) = k2_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)
    | ~ spl3_6 ),
    inference(superposition,[],[f38,f72])).

fof(f72,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f110,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f105,f70,f63,f57,f107])).

fof(f107,plain,
    ( spl3_9
  <=> k4_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f105,plain,
    ( k4_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f104,f65])).

fof(f104,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f99,f59])).

fof(f99,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))
    | ~ spl3_6 ),
    inference(superposition,[],[f38,f72])).

fof(f97,plain,
    ( spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f92,f70,f94])).

fof(f92,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f91,f54])).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(backward_demodulation,[],[f37,f25])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f24,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f91,plain,
    ( k2_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f88,f25])).

fof(f88,plain,
    ( k2_xboole_0(sK1,sK0) = k4_xboole_0(k2_xboole_0(sK1,k1_xboole_0),k3_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_6 ),
    inference(superposition,[],[f35,f72])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f26,f28])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f86,plain,
    ( ~ spl3_7
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f81,f50,f40,f83])).

fof(f83,plain,
    ( spl3_7
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k3_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f40,plain,
    ( spl3_1
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f50,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f81,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK1,sK0))
    | spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f42,f80])).

fof(f80,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
    | ~ spl3_3 ),
    inference(resolution,[],[f34,f52])).

fof(f52,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f42,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f73,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f68,f45,f70])).

fof(f45,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f68,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f33,f47])).

fof(f47,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f66,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f61,f45,f63])).

fof(f61,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f31,f47])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

% (2492)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f60,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f55,f45,f57])).

fof(f55,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f30,f47])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f53,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f48,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f45])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (2500)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (2491)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (2493)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (2500)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f43,f48,f53,f60,f66,f73,f86,f97,f110,f118,f137,f140,f146])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    spl3_12 | ~spl3_8 | ~spl3_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f141,f115,f94,f143])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    spl3_12 <=> k3_xboole_0(sK1,sK0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),sK1),k3_xboole_0(k4_xboole_0(sK1,sK0),sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    spl3_8 <=> sK1 = k2_xboole_0(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    spl3_10 <=> k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    k3_xboole_0(sK1,sK0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),sK1),k3_xboole_0(k4_xboole_0(sK1,sK0),sK1)) | (~spl3_8 | ~spl3_10)),
% 0.20/0.47    inference(forward_demodulation,[],[f127,f117])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK0)) | ~spl3_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f115])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    k3_xboole_0(sK1,sK0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK1,sK0)),sK1),k3_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK1,sK0)),sK1)) | ~spl3_8),
% 0.20/0.47    inference(superposition,[],[f36,f96])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    sK1 = k2_xboole_0(sK1,sK0) | ~spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f94])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k2_xboole_0(X0,X1)),k3_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k2_xboole_0(X0,X1)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f27,f28,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    spl3_11 | ~spl3_4 | ~spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f139,f63,f57,f134])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    spl3_11 <=> sK0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),sK1),k3_xboole_0(k4_xboole_0(sK1,sK0),sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl3_4 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    spl3_5 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    sK0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),sK1),k3_xboole_0(k4_xboole_0(sK1,sK0),sK1)) | (~spl3_4 | ~spl3_5)),
% 0.20/0.47    inference(forward_demodulation,[],[f126,f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f57])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    k3_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)),sK1),k3_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)),sK1)) | ~spl3_5),
% 0.20/0.47    inference(superposition,[],[f36,f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f63])).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    spl3_11 | ~spl3_4 | ~spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f132,f63,f57,f134])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    sK0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),sK1),k3_xboole_0(k4_xboole_0(sK1,sK0),sK1)) | (~spl3_4 | ~spl3_5)),
% 0.20/0.47    inference(forward_demodulation,[],[f119,f65])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    sK0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),sK0),k2_xboole_0(sK0,sK1)),k3_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),sK0),k2_xboole_0(sK0,sK1))) | ~spl3_4),
% 0.20/0.47    inference(superposition,[],[f36,f59])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    spl3_10 | ~spl3_6 | ~spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f113,f94,f70,f115])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK0)) | (~spl3_6 | ~spl3_8)),
% 0.20/0.47    inference(forward_demodulation,[],[f112,f96])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    k4_xboole_0(sK1,sK0) = k4_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0)) | ~spl3_6),
% 0.20/0.47    inference(forward_demodulation,[],[f102,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    k4_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0)) = k2_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0) | ~spl3_6),
% 0.20/0.47    inference(superposition,[],[f38,f72])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f70])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f29,f28])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    spl3_9 | ~spl3_4 | ~spl3_5 | ~spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f105,f70,f63,f57,f107])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    spl3_9 <=> k4_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    k4_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) | (~spl3_4 | ~spl3_5 | ~spl3_6)),
% 0.20/0.47    inference(forward_demodulation,[],[f104,f65])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0) | (~spl3_4 | ~spl3_6)),
% 0.20/0.47    inference(forward_demodulation,[],[f99,f59])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) | ~spl3_6),
% 0.20/0.47    inference(superposition,[],[f38,f72])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    spl3_8 | ~spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f92,f70,f94])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    sK1 = k2_xboole_0(sK1,sK0) | ~spl3_6),
% 0.20/0.47    inference(forward_demodulation,[],[f91,f54])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.20/0.47    inference(backward_demodulation,[],[f37,f25])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.20/0.47    inference(definition_unfolding,[],[f24,f28])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    k2_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) | ~spl3_6),
% 0.20/0.47    inference(forward_demodulation,[],[f88,f25])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    k2_xboole_0(sK1,sK0) = k4_xboole_0(k2_xboole_0(sK1,k1_xboole_0),k3_xboole_0(sK1,k1_xboole_0)) | ~spl3_6),
% 0.20/0.47    inference(superposition,[],[f35,f72])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f26,f28])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    ~spl3_7 | spl3_1 | ~spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f81,f50,f40,f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    spl3_7 <=> k7_relat_1(sK2,sK0) = k7_relat_1(sK2,k3_xboole_0(sK1,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    spl3_1 <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl3_3 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    k7_relat_1(sK2,sK0) != k7_relat_1(sK2,k3_xboole_0(sK1,sK0)) | (spl3_1 | ~spl3_3)),
% 0.20/0.47    inference(superposition,[],[f42,f80])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) ) | ~spl3_3),
% 0.20/0.47    inference(resolution,[],[f34,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    v1_relat_1(sK2) | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f50])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f40])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    spl3_6 | ~spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f68,f45,f70])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_2),
% 0.20/0.47    inference(resolution,[],[f33,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f45])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.47    inference(nnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl3_5 | ~spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f61,f45,f63])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_2),
% 0.20/0.47    inference(resolution,[],[f31,f47])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  % (2492)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    spl3_4 | ~spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f55,f45,f57])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_2),
% 0.20/0.47    inference(resolution,[],[f30,f47])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f21,f50])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 0.20/0.47    inference(negated_conjecture,[],[f11])).
% 0.20/0.47  fof(f11,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f22,f45])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ~spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f23,f40])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (2500)------------------------------
% 0.20/0.47  % (2500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (2500)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (2500)Memory used [KB]: 6268
% 0.20/0.47  % (2500)Time elapsed: 0.063 s
% 0.20/0.47  % (2500)------------------------------
% 0.20/0.47  % (2500)------------------------------
% 0.20/0.47  % (2489)Success in time 0.115 s
%------------------------------------------------------------------------------
