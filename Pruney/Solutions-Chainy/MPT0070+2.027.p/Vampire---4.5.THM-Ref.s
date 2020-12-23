%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 117 expanded)
%              Number of leaves         :   18 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :  146 ( 254 expanded)
%              Number of equality atoms :   45 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f294,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f54,f65,f82,f89,f129,f276,f287,f292])).

fof(f292,plain,
    ( spl3_1
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f291,f284,f34])).

fof(f34,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f284,plain,
    ( spl3_30
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f291,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_30 ),
    inference(trivial_inequality_removal,[],[f289])).

fof(f289,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK2)
    | ~ spl3_30 ),
    inference(superposition,[],[f29,f286])).

fof(f286,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f284])).

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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f287,plain,
    ( spl3_30
    | ~ spl3_14
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f282,f273,f126,f284])).

fof(f126,plain,
    ( spl3_14
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f273,plain,
    ( spl3_29
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f282,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_14
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f281,f128])).

fof(f128,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f281,plain,
    ( k4_xboole_0(sK0,sK0) = k3_xboole_0(sK0,sK2)
    | ~ spl3_29 ),
    inference(superposition,[],[f25,f275])).

fof(f275,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f273])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f276,plain,
    ( spl3_29
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f271,f86,f79,f273])).

fof(f79,plain,
    ( spl3_8
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f86,plain,
    ( spl3_9
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f271,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f263,f88])).

fof(f88,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f263,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK2)
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(superposition,[],[f111,f81])).

fof(f81,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f111,plain,
    ( ! [X0] : k3_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_9 ),
    inference(superposition,[],[f32,f88])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f129,plain,
    ( spl3_14
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f124,f86,f62,f126])).

fof(f62,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f124,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f113,f64])).

fof(f64,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f113,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0)
    | ~ spl3_9 ),
    inference(superposition,[],[f26,f88])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f89,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f84,f62,f86])).

fof(f84,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f83,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f83,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(superposition,[],[f25,f64])).

fof(f82,plain,
    ( spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f77,f51,f79])).

fof(f51,plain,
    ( spl3_4
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f77,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f75,f23])).

fof(f75,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f26,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f65,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f60,f44,f62])).

fof(f44,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f60,plain,
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f46,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f54,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f48,f39,f51])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (5200)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (5201)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (5207)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (5199)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (5196)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (5213)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (5208)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (5206)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (5210)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (5209)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (5207)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f294,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f37,f42,f47,f54,f65,f82,f89,f129,f276,f287,f292])).
% 0.21/0.48  fof(f292,plain,(
% 0.21/0.48    spl3_1 | ~spl3_30),
% 0.21/0.48    inference(avatar_split_clause,[],[f291,f284,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    spl3_1 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f284,plain,(
% 0.21/0.48    spl3_30 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.48  fof(f291,plain,(
% 0.21/0.48    r1_xboole_0(sK0,sK2) | ~spl3_30),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f289])).
% 0.21/0.48  fof(f289,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK2) | ~spl3_30),
% 0.21/0.48    inference(superposition,[],[f29,f286])).
% 0.21/0.48  fof(f286,plain,(
% 0.21/0.48    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f284])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.48  fof(f287,plain,(
% 0.21/0.48    spl3_30 | ~spl3_14 | ~spl3_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f282,f273,f126,f284])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    spl3_14 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f273,plain,(
% 0.21/0.48    spl3_29 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    k1_xboole_0 = k3_xboole_0(sK0,sK2) | (~spl3_14 | ~spl3_29)),
% 0.21/0.48    inference(forward_demodulation,[],[f281,f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f126])).
% 0.21/0.48  fof(f281,plain,(
% 0.21/0.48    k4_xboole_0(sK0,sK0) = k3_xboole_0(sK0,sK2) | ~spl3_29),
% 0.21/0.48    inference(superposition,[],[f25,f275])).
% 0.21/0.48  fof(f275,plain,(
% 0.21/0.48    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f273])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    spl3_29 | ~spl3_8 | ~spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f271,f86,f79,f273])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl3_8 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl3_9 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f271,plain,(
% 0.21/0.48    sK0 = k4_xboole_0(sK0,sK2) | (~spl3_8 | ~spl3_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f263,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK2) | (~spl3_8 | ~spl3_9)),
% 0.21/0.48    inference(superposition,[],[f111,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    sK1 = k4_xboole_0(sK1,sK2) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)) ) | ~spl3_9),
% 0.21/0.48    inference(superposition,[],[f32,f88])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl3_14 | ~spl3_6 | ~spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f124,f86,f62,f126])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl3_6 | ~spl3_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f113,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f62])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0) | ~spl3_9),
% 0.21/0.48    inference(superposition,[],[f26,f88])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl3_9 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f84,f62,f86])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_6),
% 0.21/0.48    inference(forward_demodulation,[],[f83,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_6),
% 0.21/0.48    inference(superposition,[],[f25,f64])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl3_8 | ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f77,f51,f79])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl3_4 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    sK1 = k4_xboole_0(sK1,sK2) | ~spl3_4),
% 0.21/0.48    inference(forward_demodulation,[],[f75,f23])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) | ~spl3_4),
% 0.21/0.48    inference(superposition,[],[f26,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f51])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl3_6 | ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f60,f44,f62])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_3),
% 0.21/0.48    inference(resolution,[],[f46,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f44])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl3_4 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f48,f39,f51])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl3_2 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl3_2),
% 0.21/0.48    inference(resolution,[],[f41,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    r1_xboole_0(sK1,sK2) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f39])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f44])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f39])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    r1_xboole_0(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f34])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ~r1_xboole_0(sK0,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (5207)------------------------------
% 0.21/0.48  % (5207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5207)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (5207)Memory used [KB]: 10746
% 0.21/0.48  % (5207)Time elapsed: 0.076 s
% 0.21/0.48  % (5207)------------------------------
% 0.21/0.48  % (5207)------------------------------
% 0.21/0.49  % (5195)Success in time 0.128 s
%------------------------------------------------------------------------------
