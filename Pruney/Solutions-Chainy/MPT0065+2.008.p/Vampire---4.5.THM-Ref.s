%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 169 expanded)
%              Number of leaves         :   29 (  75 expanded)
%              Depth                    :    7
%              Number of atoms          :  211 ( 361 expanded)
%              Number of equality atoms :   63 ( 117 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (23982)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f337,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f47,f53,f61,f74,f79,f91,f102,f112,f124,f148,f152,f170,f190,f197,f198,f334,f335])).

fof(f335,plain,
    ( sK0 != sK2
    | sK0 != k2_xboole_0(k1_xboole_0,sK0)
    | k2_xboole_0(k1_xboole_0,sK2) != k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK1,sK0) != k2_xboole_0(k1_xboole_0,sK1)
    | sK1 != k2_xboole_0(k1_xboole_0,sK1)
    | r2_xboole_0(sK0,sK2)
    | ~ r2_xboole_0(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f334,plain,
    ( spl3_32
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f329,f185,f331])).

fof(f331,plain,
    ( spl3_32
  <=> sK0 = k2_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f185,plain,
    ( spl3_18
  <=> sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f329,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_18 ),
    inference(superposition,[],[f25,f186])).

fof(f186,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f185])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f198,plain,
    ( sK1 != k2_xboole_0(k1_xboole_0,sK1)
    | ~ r1_tarski(sK1,sK2)
    | r1_tarski(k2_xboole_0(k1_xboole_0,sK1),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f197,plain,
    ( spl3_19
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f192,f165,f194])).

fof(f194,plain,
    ( spl3_19
  <=> sK1 = k2_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f165,plain,
    ( spl3_17
  <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f192,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_17 ),
    inference(superposition,[],[f25,f166])).

fof(f166,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f165])).

fof(f190,plain,
    ( spl3_18
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f183,f150,f185])).

fof(f150,plain,
    ( spl3_16
  <=> sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f183,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0))
    | ~ spl3_16 ),
    inference(superposition,[],[f24,f151])).

fof(f151,plain,
    ( sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f170,plain,
    ( spl3_17
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f163,f146,f165])).

fof(f146,plain,
    ( spl3_15
  <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f163,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_15 ),
    inference(superposition,[],[f24,f147])).

fof(f147,plain,
    ( sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f146])).

fof(f152,plain,
    ( spl3_16
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f140,f59,f150])).

fof(f59,plain,
    ( spl3_5
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f140,plain,
    ( sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl3_5 ),
    inference(superposition,[],[f34,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f148,plain,
    ( spl3_15
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f139,f51,f146])).

fof(f51,plain,
    ( spl3_4
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f139,plain,
    ( sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f34,f52])).

fof(f52,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f124,plain,
    ( ~ spl3_13
    | ~ spl3_10
    | spl3_11 ),
    inference(avatar_split_clause,[],[f117,f107,f97,f122])).

fof(f122,plain,
    ( spl3_13
  <=> r1_tarski(k2_xboole_0(k1_xboole_0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f97,plain,
    ( spl3_10
  <=> k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f107,plain,
    ( spl3_11
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f117,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_xboole_0,sK1),sK2)
    | ~ spl3_10
    | spl3_11 ),
    inference(superposition,[],[f113,f98])).

fof(f98,plain,
    ( k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK0,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f113,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),sK2)
    | spl3_11 ),
    inference(resolution,[],[f108,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f108,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f112,plain,
    ( ~ spl3_11
    | spl3_12
    | spl3_1 ),
    inference(avatar_split_clause,[],[f103,f37,f110,f107])).

fof(f110,plain,
    ( spl3_12
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f37,plain,
    ( spl3_1
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f103,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2)
    | spl3_1 ),
    inference(resolution,[],[f30,f38])).

fof(f38,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f102,plain,
    ( spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f95,f77,f97])).

fof(f77,plain,
    ( spl3_8
  <=> k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f95,plain,
    ( k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK0,sK1)
    | ~ spl3_8 ),
    inference(superposition,[],[f24,f78])).

fof(f78,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f91,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f84,f72,f86])).

fof(f86,plain,
    ( spl3_9
  <=> k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f72,plain,
    ( spl3_7
  <=> k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f84,plain,
    ( k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl3_7 ),
    inference(superposition,[],[f24,f73])).

fof(f73,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f79,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f75,f59,f77])).

fof(f75,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f69,f24])).

fof(f69,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_5 ),
    inference(superposition,[],[f25,f60])).

fof(f74,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f70,f51,f72])).

fof(f70,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f68,f24])).

fof(f68,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f25,f52])).

fof(f61,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f57,f45,f59])).

fof(f45,plain,
    ( spl3_3
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f57,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f49,f46])).

fof(f46,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f53,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f48,f41,f51])).

fof(f41,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f48,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f32,f42])).

fof(f42,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r1_tarski(sK1,sK2)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r1_tarski(sK1,sK2)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f22,f37])).

fof(f22,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:09:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (23985)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (24008)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.51  % (24000)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (23987)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (23983)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (23993)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (23981)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (24000)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  % (23982)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  fof(f337,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f39,f43,f47,f53,f61,f74,f79,f91,f102,f112,f124,f148,f152,f170,f190,f197,f198,f334,f335])).
% 0.22/0.53  fof(f335,plain,(
% 0.22/0.53    sK0 != sK2 | sK0 != k2_xboole_0(k1_xboole_0,sK0) | k2_xboole_0(k1_xboole_0,sK2) != k2_xboole_0(sK1,sK2) | k2_xboole_0(sK1,sK0) != k2_xboole_0(k1_xboole_0,sK1) | sK1 != k2_xboole_0(k1_xboole_0,sK1) | r2_xboole_0(sK0,sK2) | ~r2_xboole_0(sK0,sK1)),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f334,plain,(
% 0.22/0.53    spl3_32 | ~spl3_18),
% 0.22/0.53    inference(avatar_split_clause,[],[f329,f185,f331])).
% 0.22/0.53  fof(f331,plain,(
% 0.22/0.53    spl3_32 <=> sK0 = k2_xboole_0(k1_xboole_0,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    spl3_18 <=> sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.53  fof(f329,plain,(
% 0.22/0.53    sK0 = k2_xboole_0(k1_xboole_0,sK0) | ~spl3_18),
% 0.22/0.53    inference(superposition,[],[f25,f186])).
% 0.22/0.53  fof(f186,plain,(
% 0.22/0.53    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) | ~spl3_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f185])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    sK1 != k2_xboole_0(k1_xboole_0,sK1) | ~r1_tarski(sK1,sK2) | r1_tarski(k2_xboole_0(k1_xboole_0,sK1),sK2)),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    spl3_19 | ~spl3_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f192,f165,f194])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    spl3_19 <=> sK1 = k2_xboole_0(k1_xboole_0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    spl3_17 <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    sK1 = k2_xboole_0(k1_xboole_0,sK1) | ~spl3_17),
% 0.22/0.53    inference(superposition,[],[f25,f166])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0)) | ~spl3_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f165])).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    spl3_18 | ~spl3_16),
% 0.22/0.53    inference(avatar_split_clause,[],[f183,f150,f185])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    spl3_16 <=> sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.53  fof(f183,plain,(
% 0.22/0.53    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) | ~spl3_16),
% 0.22/0.53    inference(superposition,[],[f24,f151])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0) | ~spl3_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f150])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    spl3_17 | ~spl3_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f163,f146,f165])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    spl3_15 <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0)) | ~spl3_15),
% 0.22/0.53    inference(superposition,[],[f24,f147])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) | ~spl3_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f146])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    spl3_16 | ~spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f140,f59,f150])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    spl3_5 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0) | ~spl3_5),
% 0.22/0.53    inference(superposition,[],[f34,f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f59])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f27,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    spl3_15 | ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f139,f51,f146])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    spl3_4 <=> k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) | ~spl3_4),
% 0.22/0.53    inference(superposition,[],[f34,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f51])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ~spl3_13 | ~spl3_10 | spl3_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f117,f107,f97,f122])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    spl3_13 <=> r1_tarski(k2_xboole_0(k1_xboole_0,sK1),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    spl3_10 <=> k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    spl3_11 <=> r1_tarski(sK0,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ~r1_tarski(k2_xboole_0(k1_xboole_0,sK1),sK2) | (~spl3_10 | spl3_11)),
% 0.22/0.53    inference(superposition,[],[f113,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK0,sK1) | ~spl3_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f97])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),sK2)) ) | spl3_11),
% 0.22/0.53    inference(resolution,[],[f108,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ~r1_tarski(sK0,sK2) | spl3_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f107])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ~spl3_11 | spl3_12 | spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f103,f37,f110,f107])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    spl3_12 <=> sK0 = sK2),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    spl3_1 <=> r2_xboole_0(sK0,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    sK0 = sK2 | ~r1_tarski(sK0,sK2) | spl3_1),
% 0.22/0.53    inference(resolution,[],[f30,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ~r2_xboole_0(sK0,sK2) | spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f37])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    spl3_10 | ~spl3_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f95,f77,f97])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl3_8 <=> k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK0,sK1) | ~spl3_8),
% 0.22/0.53    inference(superposition,[],[f24,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1) | ~spl3_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f77])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    spl3_9 | ~spl3_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f84,f72,f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl3_9 <=> k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    spl3_7 <=> k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(sK1,sK2) | ~spl3_7),
% 0.22/0.53    inference(superposition,[],[f24,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK2) | ~spl3_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f72])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl3_8 | ~spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f75,f59,f77])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1) | ~spl3_5),
% 0.22/0.53    inference(forward_demodulation,[],[f69,f24])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) | ~spl3_5),
% 0.22/0.53    inference(superposition,[],[f25,f60])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    spl3_7 | ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f70,f51,f72])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK2) | ~spl3_4),
% 0.22/0.53    inference(forward_demodulation,[],[f68,f24])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) | ~spl3_4),
% 0.22/0.53    inference(superposition,[],[f25,f52])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    spl3_5 | ~spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f57,f45,f59])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    spl3_3 <=> r2_xboole_0(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.53    inference(resolution,[],[f49,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    r2_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f45])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.53    inference(resolution,[],[f32,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.53    inference(nnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    spl3_4 | ~spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f48,f41,f51])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl3_2),
% 0.22/0.53    inference(resolution,[],[f32,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f41])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f20,f45])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    r2_xboole_0(sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ~r2_xboole_0(sK0,sK2) & r1_tarski(sK1,sK2) & r2_xboole_0(sK0,sK1)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r1_tarski(sK1,sK2) & r2_xboole_0(sK0,sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r1_tarski(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f21,f41])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    r1_tarski(sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ~spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f22,f37])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ~r2_xboole_0(sK0,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (24000)------------------------------
% 0.22/0.53  % (24000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (24000)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (24000)Memory used [KB]: 10874
% 0.22/0.53  % (24000)Time elapsed: 0.121 s
% 0.22/0.53  % (24000)------------------------------
% 0.22/0.53  % (24000)------------------------------
% 0.22/0.53  % (23978)Success in time 0.174 s
%------------------------------------------------------------------------------
