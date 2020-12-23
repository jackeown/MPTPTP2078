%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 115 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :  144 ( 250 expanded)
%              Number of equality atoms :   44 (  75 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f472,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f53,f60,f75,f91,f155,f445,f465])).

fof(f465,plain,
    ( spl3_1
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f464,f442,f34])).

fof(f34,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f442,plain,
    ( spl3_53
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f464,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_53 ),
    inference(trivial_inequality_removal,[],[f462])).

fof(f462,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK2)
    | ~ spl3_53 ),
    inference(superposition,[],[f29,f444])).

fof(f444,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f442])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f445,plain,
    ( spl3_53
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f440,f152,f72,f57,f442])).

fof(f57,plain,
    ( spl3_5
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f72,plain,
    ( spl3_7
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f152,plain,
    ( spl3_19
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f440,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f429,f59])).

fof(f59,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f429,plain,
    ( k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,sK2)
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(superposition,[],[f428,f74])).

fof(f74,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f428,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f76,f213])).

fof(f213,plain,
    ( ! [X0] : k3_xboole_0(sK0,X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f208,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f208,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))
    | ~ spl3_19 ),
    inference(superposition,[],[f32,f154])).

fof(f154,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f152])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f76,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
    | ~ spl3_5 ),
    inference(superposition,[],[f32,f59])).

fof(f155,plain,
    ( spl3_19
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f150,f88,f57,f152])).

fof(f88,plain,
    ( spl3_9
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f150,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f139,f59])).

fof(f139,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0)
    | ~ spl3_9 ),
    inference(superposition,[],[f26,f90])).

fof(f90,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f91,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f86,f57,f88])).

fof(f86,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f79,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f79,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(superposition,[],[f25,f59])).

fof(f75,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f70,f50,f72])).

fof(f50,plain,
    ( spl3_4
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f70,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f68,f23])).

fof(f68,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f26,f52])).

fof(f52,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f60,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f54,f44,f57])).

fof(f44,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f54,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f46,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f46,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f53,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f48,f39,f50])).

fof(f39,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f48,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f41,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f34])).

fof(f21,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:45:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.41  % (2967)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (2974)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (2974)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f472,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f37,f42,f47,f53,f60,f75,f91,f155,f445,f465])).
% 0.21/0.47  fof(f465,plain,(
% 0.21/0.47    spl3_1 | ~spl3_53),
% 0.21/0.47    inference(avatar_split_clause,[],[f464,f442,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    spl3_1 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f442,plain,(
% 0.21/0.47    spl3_53 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.21/0.47  fof(f464,plain,(
% 0.21/0.47    r1_xboole_0(sK0,sK2) | ~spl3_53),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f462])).
% 0.21/0.47  fof(f462,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK2) | ~spl3_53),
% 0.21/0.47    inference(superposition,[],[f29,f444])).
% 0.21/0.47  fof(f444,plain,(
% 0.21/0.47    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_53),
% 0.21/0.47    inference(avatar_component_clause,[],[f442])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.47  fof(f445,plain,(
% 0.21/0.47    spl3_53 | ~spl3_5 | ~spl3_7 | ~spl3_19),
% 0.21/0.47    inference(avatar_split_clause,[],[f440,f152,f72,f57,f442])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl3_5 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl3_7 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    spl3_19 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.47  fof(f440,plain,(
% 0.21/0.47    k1_xboole_0 = k3_xboole_0(sK0,sK2) | (~spl3_5 | ~spl3_7 | ~spl3_19)),
% 0.21/0.47    inference(forward_demodulation,[],[f429,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f57])).
% 0.21/0.47  fof(f429,plain,(
% 0.21/0.47    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,sK2) | (~spl3_5 | ~spl3_7 | ~spl3_19)),
% 0.21/0.47    inference(superposition,[],[f428,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    sK1 = k4_xboole_0(sK1,sK2) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f72])).
% 0.21/0.47  fof(f428,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)) ) | (~spl3_5 | ~spl3_19)),
% 0.21/0.47    inference(forward_demodulation,[],[f76,f213])).
% 0.21/0.47  fof(f213,plain,(
% 0.21/0.47    ( ! [X0] : (k3_xboole_0(sK0,X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ) | ~spl3_19),
% 0.21/0.47    inference(forward_demodulation,[],[f208,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f208,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ) | ~spl3_19),
% 0.21/0.47    inference(superposition,[],[f32,f154])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl3_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f152])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ) | ~spl3_5),
% 0.21/0.47    inference(superposition,[],[f32,f59])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    spl3_19 | ~spl3_5 | ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f150,f88,f57,f152])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl3_9 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl3_5 | ~spl3_9)),
% 0.21/0.47    inference(forward_demodulation,[],[f139,f59])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0) | ~spl3_9),
% 0.21/0.47    inference(superposition,[],[f26,f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f88])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    spl3_9 | ~spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f86,f57,f88])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_5),
% 0.21/0.47    inference(forward_demodulation,[],[f79,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_5),
% 0.21/0.47    inference(superposition,[],[f25,f59])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    spl3_7 | ~spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f70,f50,f72])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl3_4 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    sK1 = k4_xboole_0(sK1,sK2) | ~spl3_4),
% 0.21/0.47    inference(forward_demodulation,[],[f68,f23])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) | ~spl3_4),
% 0.21/0.47    inference(superposition,[],[f26,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl3_5 | ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f54,f44,f57])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_3),
% 0.21/0.47    inference(resolution,[],[f46,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f44])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl3_4 | ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f48,f39,f50])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    spl3_2 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f41,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    r1_xboole_0(sK1,sK2) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f39])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f44])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f20,f39])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    r1_xboole_0(sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f21,f34])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ~r1_xboole_0(sK0,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (2974)------------------------------
% 0.21/0.47  % (2974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (2974)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (2974)Memory used [KB]: 10874
% 0.21/0.47  % (2974)Time elapsed: 0.017 s
% 0.21/0.47  % (2974)------------------------------
% 0.21/0.47  % (2974)------------------------------
% 0.21/0.47  % (2960)Success in time 0.113 s
%------------------------------------------------------------------------------
