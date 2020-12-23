%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 123 expanded)
%              Number of leaves         :   19 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  148 ( 256 expanded)
%              Number of equality atoms :   49 (  85 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f212,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f47,f53,f60,f79,f99,f195,f205,f210])).

fof(f210,plain,
    ( spl3_3
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f209,f202,f38])).

fof(f38,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f202,plain,
    ( spl3_19
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f209,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_19 ),
    inference(trivial_inequality_removal,[],[f207])).

fof(f207,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK1)
    | ~ spl3_19 ),
    inference(superposition,[],[f23,f204])).

fof(f204,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f202])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f205,plain,
    ( spl3_19
    | ~ spl3_9
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f200,f190,f76,f202])).

fof(f76,plain,
    ( spl3_9
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f190,plain,
    ( spl3_18
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f200,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_9
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f199,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f199,plain,
    ( k4_xboole_0(sK0,sK0) = k3_xboole_0(sK0,sK1)
    | ~ spl3_18 ),
    inference(superposition,[],[f21,f192])).

fof(f192,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f195,plain,
    ( spl3_18
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f185,f96,f57,f190])).

fof(f57,plain,
    ( spl3_6
  <=> sK0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f96,plain,
    ( spl3_11
  <=> sK0 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f185,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(superposition,[],[f98,f111])).

fof(f111,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k3_xboole_0(X0,sK2))
    | ~ spl3_6 ),
    inference(superposition,[],[f109,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f109,plain,
    ( ! [X1] : k4_xboole_0(sK0,k3_xboole_0(sK2,X1)) = k4_xboole_0(sK0,X1)
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f104,f61])).

fof(f61,plain,
    ( ! [X0] : k3_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_6 ),
    inference(superposition,[],[f26,f59])).

fof(f59,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f104,plain,
    ( ! [X1] : k4_xboole_0(sK0,k3_xboole_0(sK2,X1)) = k3_xboole_0(sK0,k4_xboole_0(sK2,X1))
    | ~ spl3_6 ),
    inference(superposition,[],[f61,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f98,plain,
    ( sK0 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f99,plain,
    ( spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f94,f50,f96])).

fof(f50,plain,
    ( spl3_5
  <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f94,plain,
    ( sK0 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f91,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f91,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(superposition,[],[f20,f52])).

fof(f52,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f79,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f74,f57,f44,f76])).

fof(f44,plain,
    ( spl3_4
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f74,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f63,f46])).

fof(f46,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f63,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0)
    | ~ spl3_6 ),
    inference(superposition,[],[f20,f59])).

fof(f60,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f55,f44,f57])).

fof(f55,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f54,f18])).

fof(f54,plain,
    ( k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f21,f46])).

fof(f53,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f48,f28,f50])).

fof(f28,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f48,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f30,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f47,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f42,f33,f44])).

fof(f33,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f42,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f35,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f35,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f41,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f15,f38])).

fof(f15,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f36,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f28])).

fof(f17,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:13:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (21213)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.42  % (21213)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f212,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f31,f36,f41,f47,f53,f60,f79,f99,f195,f205,f210])).
% 0.20/0.42  fof(f210,plain,(
% 0.20/0.42    spl3_3 | ~spl3_19),
% 0.20/0.42    inference(avatar_split_clause,[],[f209,f202,f38])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl3_3 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.42  fof(f202,plain,(
% 0.20/0.42    spl3_19 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.42  fof(f209,plain,(
% 0.20/0.42    r1_xboole_0(sK0,sK1) | ~spl3_19),
% 0.20/0.42    inference(trivial_inequality_removal,[],[f207])).
% 0.20/0.42  fof(f207,plain,(
% 0.20/0.42    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK1) | ~spl3_19),
% 0.20/0.42    inference(superposition,[],[f23,f204])).
% 0.20/0.42  fof(f204,plain,(
% 0.20/0.42    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_19),
% 0.20/0.42    inference(avatar_component_clause,[],[f202])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.42    inference(nnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.42  fof(f205,plain,(
% 0.20/0.42    spl3_19 | ~spl3_9 | ~spl3_18),
% 0.20/0.42    inference(avatar_split_clause,[],[f200,f190,f76,f202])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    spl3_9 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.42  fof(f190,plain,(
% 0.20/0.42    spl3_18 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.42  fof(f200,plain,(
% 0.20/0.42    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl3_9 | ~spl3_18)),
% 0.20/0.42    inference(forward_demodulation,[],[f199,f78])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl3_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f76])).
% 0.20/0.42  fof(f199,plain,(
% 0.20/0.42    k4_xboole_0(sK0,sK0) = k3_xboole_0(sK0,sK1) | ~spl3_18),
% 0.20/0.42    inference(superposition,[],[f21,f192])).
% 0.20/0.42  fof(f192,plain,(
% 0.20/0.42    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_18),
% 0.20/0.42    inference(avatar_component_clause,[],[f190])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.42  fof(f195,plain,(
% 0.20/0.42    spl3_18 | ~spl3_6 | ~spl3_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f185,f96,f57,f190])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    spl3_6 <=> sK0 = k3_xboole_0(sK0,sK2)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.42  fof(f96,plain,(
% 0.20/0.42    spl3_11 <=> sK0 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.42  fof(f185,plain,(
% 0.20/0.42    sK0 = k4_xboole_0(sK0,sK1) | (~spl3_6 | ~spl3_11)),
% 0.20/0.42    inference(superposition,[],[f98,f111])).
% 0.20/0.42  fof(f111,plain,(
% 0.20/0.42    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k3_xboole_0(X0,sK2))) ) | ~spl3_6),
% 0.20/0.42    inference(superposition,[],[f109,f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.42  fof(f109,plain,(
% 0.20/0.42    ( ! [X1] : (k4_xboole_0(sK0,k3_xboole_0(sK2,X1)) = k4_xboole_0(sK0,X1)) ) | ~spl3_6),
% 0.20/0.42    inference(forward_demodulation,[],[f104,f61])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    ( ! [X0] : (k3_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) ) | ~spl3_6),
% 0.20/0.42    inference(superposition,[],[f26,f59])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    sK0 = k3_xboole_0(sK0,sK2) | ~spl3_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f57])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.42  fof(f104,plain,(
% 0.20/0.42    ( ! [X1] : (k4_xboole_0(sK0,k3_xboole_0(sK2,X1)) = k3_xboole_0(sK0,k4_xboole_0(sK2,X1))) ) | ~spl3_6),
% 0.20/0.42    inference(superposition,[],[f61,f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.42  fof(f98,plain,(
% 0.20/0.42    sK0 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f96])).
% 0.20/0.42  fof(f99,plain,(
% 0.20/0.42    spl3_11 | ~spl3_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f94,f50,f96])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    spl3_5 <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.42  fof(f94,plain,(
% 0.20/0.42    sK0 = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_5),
% 0.20/0.42    inference(forward_demodulation,[],[f91,f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.42  fof(f91,plain,(
% 0.20/0.42    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_5),
% 0.20/0.42    inference(superposition,[],[f20,f52])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f50])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    spl3_9 | ~spl3_4 | ~spl3_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f74,f57,f44,f76])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    spl3_4 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl3_4 | ~spl3_6)),
% 0.20/0.42    inference(forward_demodulation,[],[f63,f46])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl3_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f44])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0) | ~spl3_6),
% 0.20/0.42    inference(superposition,[],[f20,f59])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    spl3_6 | ~spl3_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f55,f44,f57])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    sK0 = k3_xboole_0(sK0,sK2) | ~spl3_4),
% 0.20/0.42    inference(forward_demodulation,[],[f54,f18])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_4),
% 0.20/0.42    inference(superposition,[],[f21,f46])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl3_5 | ~spl3_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f48,f28,f50])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    spl3_1 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.20/0.42    inference(resolution,[],[f30,f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f28])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    spl3_4 | ~spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f42,f33,f44])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    spl3_2 <=> r1_tarski(sK0,sK2)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl3_2),
% 0.20/0.42    inference(resolution,[],[f35,f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.42    inference(nnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    r1_tarski(sK0,sK2) | ~spl3_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f33])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    ~spl3_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f15,f38])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ~r1_xboole_0(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.42    inference(negated_conjecture,[],[f8])).
% 0.20/0.42  fof(f8,conjecture,(
% 0.20/0.42    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f16,f33])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    r1_tarski(sK0,sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    spl3_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f17,f28])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (21213)------------------------------
% 0.20/0.42  % (21213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (21213)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (21213)Memory used [KB]: 10618
% 0.20/0.42  % (21213)Time elapsed: 0.007 s
% 0.20/0.42  % (21213)------------------------------
% 0.20/0.42  % (21213)------------------------------
% 0.20/0.42  % (21200)Success in time 0.062 s
%------------------------------------------------------------------------------
