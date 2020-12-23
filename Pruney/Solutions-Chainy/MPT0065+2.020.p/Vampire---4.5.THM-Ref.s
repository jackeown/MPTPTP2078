%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 115 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  137 ( 315 expanded)
%              Number of equality atoms :   27 (  50 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f571,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f356,f394,f446,f547])).

fof(f547,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f546])).

fof(f546,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_17 ),
    inference(subsumption_resolution,[],[f545,f424])).

fof(f424,plain,
    ( sK0 != sK1
    | spl3_17 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl3_17
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f545,plain,
    ( sK0 = sK1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f474,f498])).

fof(f498,plain,
    ( sK0 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f494,f407])).

fof(f407,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f53,f58])).

fof(f58,plain,
    ( sK0 = sK2
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f53,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f494,plain,
    ( sK0 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ r1_tarski(sK0,sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(superposition,[],[f32,f434])).

fof(f434,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f407,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f474,plain,
    ( sK1 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f470,f35])).

fof(f35,plain,(
    r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f21,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f21,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r1_tarski(sK1,sK2)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r1_tarski(sK1,sK2)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f470,plain,
    ( sK1 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ r1_tarski(sK0,sK1)
    | ~ spl3_4 ),
    inference(superposition,[],[f32,f403])).

fof(f403,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f38,f58])).

fof(f38,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f22,f26])).

fof(f22,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f446,plain,(
    ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f437,f31])).

fof(f31,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(f437,plain,
    ( r2_xboole_0(sK0,sK0)
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f21,f425])).

fof(f425,plain,
    ( sK0 = sK1
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f423])).

fof(f394,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f392,f54])).

fof(f54,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f392,plain,(
    r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f40,f35])).

fof(f40,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | r1_tarski(X1,sK2) ) ),
    inference(resolution,[],[f22,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f356,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f355,f56,f52])).

fof(f355,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f23,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f23,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:32:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (26183)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (26190)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (26179)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (26197)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % (26179)Refutation not found, incomplete strategy% (26179)------------------------------
% 0.22/0.48  % (26179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (26179)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (26179)Memory used [KB]: 10618
% 0.22/0.48  % (26179)Time elapsed: 0.063 s
% 0.22/0.48  % (26179)------------------------------
% 0.22/0.48  % (26179)------------------------------
% 0.22/0.48  % (26191)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (26197)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (26194)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (26178)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f571,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f356,f394,f446,f547])).
% 0.22/0.49  fof(f547,plain,(
% 0.22/0.49    ~spl3_3 | ~spl3_4 | spl3_17),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f546])).
% 0.22/0.49  fof(f546,plain,(
% 0.22/0.49    $false | (~spl3_3 | ~spl3_4 | spl3_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f545,f424])).
% 0.22/0.49  fof(f424,plain,(
% 0.22/0.49    sK0 != sK1 | spl3_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f423])).
% 0.22/0.49  fof(f423,plain,(
% 0.22/0.49    spl3_17 <=> sK0 = sK1),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.49  fof(f545,plain,(
% 0.22/0.49    sK0 = sK1 | (~spl3_3 | ~spl3_4)),
% 0.22/0.49    inference(forward_demodulation,[],[f474,f498])).
% 0.22/0.49  fof(f498,plain,(
% 0.22/0.49    sK0 = k2_xboole_0(sK0,k1_xboole_0) | (~spl3_3 | ~spl3_4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f494,f407])).
% 0.22/0.49  fof(f407,plain,(
% 0.22/0.49    r1_tarski(sK0,sK0) | (~spl3_3 | ~spl3_4)),
% 0.22/0.49    inference(backward_demodulation,[],[f53,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    sK0 = sK2 | ~spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    spl3_4 <=> sK0 = sK2),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    r1_tarski(sK0,sK2) | ~spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    spl3_3 <=> r1_tarski(sK0,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f494,plain,(
% 0.22/0.49    sK0 = k2_xboole_0(sK0,k1_xboole_0) | ~r1_tarski(sK0,sK0) | (~spl3_3 | ~spl3_4)),
% 0.22/0.49    inference(superposition,[],[f32,f434])).
% 0.22/0.49  fof(f434,plain,(
% 0.22/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl3_3 | ~spl3_4)),
% 0.22/0.49    inference(resolution,[],[f407,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.49    inference(nnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.22/0.49  fof(f474,plain,(
% 0.22/0.49    sK1 = k2_xboole_0(sK0,k1_xboole_0) | ~spl3_4),
% 0.22/0.49    inference(subsumption_resolution,[],[f470,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    r1_tarski(sK0,sK1)),
% 0.22/0.49    inference(resolution,[],[f21,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.49    inference(nnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    r2_xboole_0(sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ~r2_xboole_0(sK0,sK2) & r1_tarski(sK1,sK2) & r2_xboole_0(sK0,sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r1_tarski(sK1,sK2) & r2_xboole_0(sK0,sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r1_tarski(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.22/0.49  fof(f470,plain,(
% 0.22/0.49    sK1 = k2_xboole_0(sK0,k1_xboole_0) | ~r1_tarski(sK0,sK1) | ~spl3_4),
% 0.22/0.49    inference(superposition,[],[f32,f403])).
% 0.22/0.49  fof(f403,plain,(
% 0.22/0.49    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl3_4),
% 0.22/0.49    inference(backward_demodulation,[],[f38,f58])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.22/0.49    inference(resolution,[],[f22,f26])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    r1_tarski(sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f446,plain,(
% 0.22/0.49    ~spl3_17),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f445])).
% 0.22/0.49  fof(f445,plain,(
% 0.22/0.49    $false | ~spl3_17),
% 0.22/0.49    inference(subsumption_resolution,[],[f437,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_xboole_0(X0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0] : ~r2_xboole_0(X0,X0)),
% 0.22/0.49    inference(rectify,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : ~r2_xboole_0(X0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).
% 0.22/0.49  fof(f437,plain,(
% 0.22/0.49    r2_xboole_0(sK0,sK0) | ~spl3_17),
% 0.22/0.49    inference(backward_demodulation,[],[f21,f425])).
% 0.22/0.49  fof(f425,plain,(
% 0.22/0.49    sK0 = sK1 | ~spl3_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f423])).
% 0.22/0.49  fof(f394,plain,(
% 0.22/0.49    spl3_3),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f393])).
% 0.22/0.49  fof(f393,plain,(
% 0.22/0.49    $false | spl3_3),
% 0.22/0.49    inference(subsumption_resolution,[],[f392,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ~r1_tarski(sK0,sK2) | spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f52])).
% 0.22/0.49  fof(f392,plain,(
% 0.22/0.49    r1_tarski(sK0,sK2)),
% 0.22/0.49    inference(resolution,[],[f40,f35])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X1] : (~r1_tarski(X1,sK1) | r1_tarski(X1,sK2)) )),
% 0.22/0.49    inference(resolution,[],[f22,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.49  fof(f356,plain,(
% 0.22/0.49    ~spl3_3 | spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f355,f56,f52])).
% 0.22/0.49  fof(f355,plain,(
% 0.22/0.49    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 0.22/0.49    inference(resolution,[],[f23,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ~r2_xboole_0(sK0,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (26197)------------------------------
% 0.22/0.49  % (26197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (26197)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (26197)Memory used [KB]: 6268
% 0.22/0.49  % (26197)Time elapsed: 0.062 s
% 0.22/0.49  % (26197)------------------------------
% 0.22/0.49  % (26197)------------------------------
% 0.22/0.49  % (26175)Success in time 0.127 s
%------------------------------------------------------------------------------
