%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 175 expanded)
%              Number of leaves         :   27 (  78 expanded)
%              Depth                    :    6
%              Number of atoms          :  210 ( 364 expanded)
%              Number of equality atoms :   60 ( 111 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f408,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f52,f64,f71,f78,f98,f134,f154,f167,f174,f214,f299,f322,f345,f353,f406])).

fof(f406,plain,
    ( spl3_3
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f395,f350,f43])).

fof(f43,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f350,plain,
    ( spl3_40
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f395,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_40 ),
    inference(trivial_inequality_removal,[],[f393])).

% (28430)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
fof(f393,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK1)
    | ~ spl3_40 ),
    inference(superposition,[],[f27,f352])).

fof(f352,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f350])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

% (28431)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f353,plain,
    ( spl3_40
    | ~ spl3_11
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f348,f341,f95,f350])).

fof(f95,plain,
    ( spl3_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f341,plain,
    ( spl3_39
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f348,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_11
    | ~ spl3_39 ),
    inference(forward_demodulation,[],[f347,f97])).

fof(f97,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f347,plain,
    ( k4_xboole_0(sK0,sK0) = k3_xboole_0(sK0,sK1)
    | ~ spl3_39 ),
    inference(superposition,[],[f24,f343])).

fof(f343,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f341])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f345,plain,
    ( spl3_39
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f338,f319,f341])).

fof(f319,plain,
    ( spl3_36
  <=> sK0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f338,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_36 ),
    inference(superposition,[],[f23,f321])).

fof(f321,plain,
    ( sK0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f319])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f322,plain,
    ( spl3_36
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f317,f296,f319])).

fof(f296,plain,
    ( spl3_34
  <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f317,plain,
    ( sK0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f308,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f308,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_34 ),
    inference(superposition,[],[f23,f298])).

fof(f298,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f296])).

fof(f299,plain,
    ( spl3_34
    | ~ spl3_7
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f294,f210,f68,f296])).

fof(f68,plain,
    ( spl3_7
  <=> sK0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f210,plain,
    ( spl3_24
  <=> k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f294,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_7
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f289,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f289,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_24 ),
    inference(superposition,[],[f79,f212])).

fof(f212,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f210])).

fof(f79,plain,
    ( ! [X0] : k3_xboole_0(sK0,k3_xboole_0(sK2,X0)) = k3_xboole_0(sK0,X0)
    | ~ spl3_7 ),
    inference(superposition,[],[f31,f70])).

fof(f70,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f214,plain,
    ( spl3_24
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f203,f171,f210])).

fof(f171,plain,
    ( spl3_19
  <=> k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f203,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl3_19 ),
    inference(superposition,[],[f31,f173])).

fof(f173,plain,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK2,sK0),sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f171])).

fof(f174,plain,
    ( spl3_19
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f168,f164,f171])).

fof(f164,plain,
    ( spl3_18
  <=> r1_xboole_0(k3_xboole_0(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f168,plain,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK2,sK0),sK1)
    | ~ spl3_18 ),
    inference(resolution,[],[f166,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f166,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,sK0),sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f164])).

fof(f167,plain,
    ( spl3_18
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f162,f151,f164])).

fof(f151,plain,
    ( spl3_16
  <=> r1_xboole_0(sK1,k3_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f162,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,sK0),sK1)
    | ~ spl3_16 ),
    inference(resolution,[],[f153,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f153,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK2,sK0))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f151])).

fof(f154,plain,
    ( spl3_16
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f147,f130,f151])).

fof(f130,plain,
    ( spl3_14
  <=> k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f147,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK2,sK0))
    | ~ spl3_14 ),
    inference(trivial_inequality_removal,[],[f145])).

fof(f145,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,k3_xboole_0(sK2,sK0))
    | ~ spl3_14 ),
    inference(superposition,[],[f27,f132])).

fof(f132,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK2,sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f130])).

fof(f134,plain,
    ( spl3_14
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f123,f75,f130])).

fof(f75,plain,
    ( spl3_8
  <=> k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f123,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK2,sK0))
    | ~ spl3_8 ),
    inference(superposition,[],[f31,f77])).

fof(f77,plain,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f98,plain,
    ( spl3_11
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f93,f68,f49,f95])).

fof(f49,plain,
    ( spl3_4
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f93,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f82,f51])).

fof(f51,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f82,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0)
    | ~ spl3_7 ),
    inference(superposition,[],[f23,f70])).

fof(f78,plain,
    ( spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f72,f61,f75])).

fof(f61,plain,
    ( spl3_6
  <=> r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f72,plain,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f63,f26])).

fof(f63,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f71,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f66,f49,f68])).

fof(f66,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f65,f22])).

fof(f65,plain,
    ( k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f24,f51])).

fof(f64,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f54,f33,f61])).

fof(f33,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f54,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f35,f25])).

fof(f35,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f52,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f47,f38,f49])).

fof(f38,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f47,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f40,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f40,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f46,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f18,f43])).

fof(f18,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f41,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f33])).

fof(f20,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (28420)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (28417)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (28424)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (28422)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (28416)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (28425)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (28425)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (28418)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f408,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f36,f41,f46,f52,f64,f71,f78,f98,f134,f154,f167,f174,f214,f299,f322,f345,f353,f406])).
% 0.20/0.49  fof(f406,plain,(
% 0.20/0.49    spl3_3 | ~spl3_40),
% 0.20/0.49    inference(avatar_split_clause,[],[f395,f350,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    spl3_3 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f350,plain,(
% 0.20/0.49    spl3_40 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.20/0.49  fof(f395,plain,(
% 0.20/0.49    r1_xboole_0(sK0,sK1) | ~spl3_40),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f393])).
% 0.20/0.49  % (28430)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  fof(f393,plain,(
% 0.20/0.49    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK1) | ~spl3_40),
% 0.20/0.49    inference(superposition,[],[f27,f352])).
% 0.20/0.49  fof(f352,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_40),
% 0.20/0.49    inference(avatar_component_clause,[],[f350])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.49  % (28431)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  fof(f353,plain,(
% 0.20/0.49    spl3_40 | ~spl3_11 | ~spl3_39),
% 0.20/0.49    inference(avatar_split_clause,[],[f348,f341,f95,f350])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    spl3_11 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.49  fof(f341,plain,(
% 0.20/0.49    spl3_39 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.20/0.49  fof(f348,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl3_11 | ~spl3_39)),
% 0.20/0.49    inference(forward_demodulation,[],[f347,f97])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl3_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f95])).
% 0.20/0.49  fof(f347,plain,(
% 0.20/0.49    k4_xboole_0(sK0,sK0) = k3_xboole_0(sK0,sK1) | ~spl3_39),
% 0.20/0.49    inference(superposition,[],[f24,f343])).
% 0.20/0.49  fof(f343,plain,(
% 0.20/0.49    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_39),
% 0.20/0.49    inference(avatar_component_clause,[],[f341])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.49  fof(f345,plain,(
% 0.20/0.49    spl3_39 | ~spl3_36),
% 0.20/0.49    inference(avatar_split_clause,[],[f338,f319,f341])).
% 0.20/0.49  fof(f319,plain,(
% 0.20/0.49    spl3_36 <=> sK0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.49  fof(f338,plain,(
% 0.20/0.49    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_36),
% 0.20/0.49    inference(superposition,[],[f23,f321])).
% 0.20/0.49  fof(f321,plain,(
% 0.20/0.49    sK0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_36),
% 0.20/0.49    inference(avatar_component_clause,[],[f319])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.49  fof(f322,plain,(
% 0.20/0.49    spl3_36 | ~spl3_34),
% 0.20/0.49    inference(avatar_split_clause,[],[f317,f296,f319])).
% 0.20/0.49  fof(f296,plain,(
% 0.20/0.49    spl3_34 <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.49  fof(f317,plain,(
% 0.20/0.49    sK0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_34),
% 0.20/0.49    inference(forward_demodulation,[],[f308,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.49  fof(f308,plain,(
% 0.20/0.49    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_34),
% 0.20/0.49    inference(superposition,[],[f23,f298])).
% 0.20/0.49  fof(f298,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_34),
% 0.20/0.49    inference(avatar_component_clause,[],[f296])).
% 0.20/0.49  fof(f299,plain,(
% 0.20/0.49    spl3_34 | ~spl3_7 | ~spl3_24),
% 0.20/0.49    inference(avatar_split_clause,[],[f294,f210,f68,f296])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl3_7 <=> sK0 = k3_xboole_0(sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f210,plain,(
% 0.20/0.49    spl3_24 <=> k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.49  fof(f294,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | (~spl3_7 | ~spl3_24)),
% 0.20/0.49    inference(forward_demodulation,[],[f289,f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.49  fof(f289,plain,(
% 0.20/0.49    k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,k1_xboole_0) | (~spl3_7 | ~spl3_24)),
% 0.20/0.49    inference(superposition,[],[f79,f212])).
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK0,sK1)) | ~spl3_24),
% 0.20/0.49    inference(avatar_component_clause,[],[f210])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X0] : (k3_xboole_0(sK0,k3_xboole_0(sK2,X0)) = k3_xboole_0(sK0,X0)) ) | ~spl3_7),
% 0.20/0.49    inference(superposition,[],[f31,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    sK0 = k3_xboole_0(sK0,sK2) | ~spl3_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f68])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    spl3_24 | ~spl3_19),
% 0.20/0.49    inference(avatar_split_clause,[],[f203,f171,f210])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    spl3_19 <=> k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK2,sK0),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK0,sK1)) | ~spl3_19),
% 0.20/0.49    inference(superposition,[],[f31,f173])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK2,sK0),sK1) | ~spl3_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f171])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    spl3_19 | ~spl3_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f168,f164,f171])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    spl3_18 <=> r1_xboole_0(k3_xboole_0(sK2,sK0),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK2,sK0),sK1) | ~spl3_18),
% 0.20/0.49    inference(resolution,[],[f166,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    r1_xboole_0(k3_xboole_0(sK2,sK0),sK1) | ~spl3_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f164])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    spl3_18 | ~spl3_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f162,f151,f164])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    spl3_16 <=> r1_xboole_0(sK1,k3_xboole_0(sK2,sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    r1_xboole_0(k3_xboole_0(sK2,sK0),sK1) | ~spl3_16),
% 0.20/0.49    inference(resolution,[],[f153,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    r1_xboole_0(sK1,k3_xboole_0(sK2,sK0)) | ~spl3_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f151])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    spl3_16 | ~spl3_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f147,f130,f151])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    spl3_14 <=> k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK2,sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    r1_xboole_0(sK1,k3_xboole_0(sK2,sK0)) | ~spl3_14),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f145])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,k3_xboole_0(sK2,sK0)) | ~spl3_14),
% 0.20/0.49    inference(superposition,[],[f27,f132])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK2,sK0)) | ~spl3_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f130])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    spl3_14 | ~spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f123,f75,f130])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    spl3_8 <=> k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(sK1,k3_xboole_0(sK2,sK0)) | ~spl3_8),
% 0.20/0.49    inference(superposition,[],[f31,f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f75])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    spl3_11 | ~spl3_4 | ~spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f93,f68,f49,f95])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    spl3_4 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl3_4 | ~spl3_7)),
% 0.20/0.49    inference(forward_demodulation,[],[f82,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f49])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0) | ~spl3_7),
% 0.20/0.49    inference(superposition,[],[f23,f70])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    spl3_8 | ~spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f72,f61,f75])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    spl3_6 <=> r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) | ~spl3_6),
% 0.20/0.49    inference(resolution,[],[f63,f26])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) | ~spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f61])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    spl3_7 | ~spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f66,f49,f68])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    sK0 = k3_xboole_0(sK0,sK2) | ~spl3_4),
% 0.20/0.49    inference(forward_demodulation,[],[f65,f22])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_4),
% 0.20/0.49    inference(superposition,[],[f24,f51])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    spl3_6 | ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f54,f33,f61])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    spl3_1 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) | ~spl3_1),
% 0.20/0.49    inference(resolution,[],[f35,f25])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f33])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    spl3_4 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f47,f38,f49])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    spl3_2 <=> r1_tarski(sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl3_2),
% 0.20/0.49    inference(resolution,[],[f40,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    r1_tarski(sK0,sK2) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f38])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ~spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f18,f43])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f19,f38])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    r1_tarski(sK0,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f20,f33])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (28425)------------------------------
% 0.20/0.49  % (28425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28425)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (28425)Memory used [KB]: 10874
% 0.20/0.49  % (28425)Time elapsed: 0.075 s
% 0.20/0.49  % (28425)------------------------------
% 0.20/0.49  % (28425)------------------------------
% 0.20/0.49  % (28415)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (28413)Success in time 0.133 s
%------------------------------------------------------------------------------
