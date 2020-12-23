%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:21 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 210 expanded)
%              Number of leaves         :   12 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  126 ( 479 expanded)
%              Number of equality atoms :   42 ( 140 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f266,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f228,f265])).

fof(f265,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl3_2 ),
    inference(resolution,[],[f255,f23])).

fof(f23,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(f255,plain,
    ( r2_xboole_0(sK0,sK0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f229,f239])).

fof(f239,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f218,f238])).

fof(f238,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f233,f117])).

fof(f117,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[],[f100,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f100,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f90,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f90,plain,(
    sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f34,f36])).

fof(f36,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f32,f20])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r2_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r2_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).

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

fof(f233,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f48,f67])).

fof(f67,plain,
    ( sK0 = sK2
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f48,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f46,f24])).

fof(f46,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f25,f41])).

fof(f41,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f37,f21])).

fof(f21,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
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

fof(f218,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f49,f206])).

fof(f206,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f178,f41])).

fof(f178,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(superposition,[],[f92,f25])).

fof(f92,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    inference(superposition,[],[f34,f24])).

fof(f49,plain,(
    k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f47,f24])).

fof(f47,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f45,f24])).

fof(f45,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f25,f36])).

fof(f229,plain,
    ( r2_xboole_0(sK1,sK0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f21,f67])).

fof(f228,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f219,f43])).

fof(f43,plain,(
    r1_tarski(sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f42])).

fof(f42,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f31,f41])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f219,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_1 ),
    inference(backward_demodulation,[],[f73,f206])).

fof(f73,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_xboole_0,sK1),sK2)
    | spl3_1 ),
    inference(superposition,[],[f69,f49])).

fof(f69,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),sK2)
    | spl3_1 ),
    inference(resolution,[],[f63,f33])).

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

fof(f63,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f68,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f57,f65,f61])).

fof(f57,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f30,f22])).

fof(f22,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (25262)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (25261)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (25274)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (25282)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (25270)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (25276)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (25255)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.52  % (25278)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.28/0.52  % (25258)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.52  % (25276)Refutation not found, incomplete strategy% (25276)------------------------------
% 1.28/0.52  % (25276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (25276)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.52  
% 1.28/0.52  % (25276)Memory used [KB]: 10618
% 1.28/0.52  % (25276)Time elapsed: 0.084 s
% 1.28/0.52  % (25276)------------------------------
% 1.28/0.52  % (25276)------------------------------
% 1.28/0.52  % (25258)Refutation not found, incomplete strategy% (25258)------------------------------
% 1.28/0.52  % (25258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (25258)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.52  
% 1.28/0.52  % (25258)Memory used [KB]: 6140
% 1.28/0.52  % (25258)Time elapsed: 0.116 s
% 1.28/0.52  % (25258)------------------------------
% 1.28/0.52  % (25258)------------------------------
% 1.28/0.52  % (25254)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.53  % (25266)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.53  % (25259)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.53  % (25257)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.53  % (25279)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.28/0.53  % (25268)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.28/0.53  % (25263)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.53  % (25266)Refutation found. Thanks to Tanya!
% 1.28/0.53  % SZS status Theorem for theBenchmark
% 1.28/0.53  % SZS output start Proof for theBenchmark
% 1.28/0.53  fof(f266,plain,(
% 1.28/0.53    $false),
% 1.28/0.53    inference(avatar_sat_refutation,[],[f68,f228,f265])).
% 1.28/0.53  fof(f265,plain,(
% 1.28/0.53    ~spl3_2),
% 1.28/0.53    inference(avatar_contradiction_clause,[],[f263])).
% 1.28/0.53  fof(f263,plain,(
% 1.28/0.53    $false | ~spl3_2),
% 1.28/0.53    inference(resolution,[],[f255,f23])).
% 1.28/0.53  fof(f23,plain,(
% 1.28/0.53    ( ! [X0] : (~r2_xboole_0(X0,X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f11])).
% 1.28/0.53  fof(f11,plain,(
% 1.28/0.53    ! [X0] : ~r2_xboole_0(X0,X0)),
% 1.28/0.53    inference(rectify,[],[f3])).
% 1.28/0.53  fof(f3,axiom,(
% 1.28/0.53    ! [X0,X1] : ~r2_xboole_0(X0,X0)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).
% 1.28/0.53  fof(f255,plain,(
% 1.28/0.53    r2_xboole_0(sK0,sK0) | ~spl3_2),
% 1.28/0.53    inference(backward_demodulation,[],[f229,f239])).
% 1.28/0.53  fof(f239,plain,(
% 1.28/0.53    sK0 = sK1 | ~spl3_2),
% 1.28/0.53    inference(backward_demodulation,[],[f218,f238])).
% 1.28/0.53  fof(f238,plain,(
% 1.28/0.53    sK0 = k2_xboole_0(sK0,sK1) | ~spl3_2),
% 1.28/0.53    inference(forward_demodulation,[],[f233,f117])).
% 1.28/0.53  fof(f117,plain,(
% 1.28/0.53    sK0 = k2_xboole_0(k1_xboole_0,sK0)),
% 1.28/0.53    inference(superposition,[],[f100,f25])).
% 1.28/0.53  fof(f25,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f6])).
% 1.28/0.53  fof(f6,axiom,(
% 1.28/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.28/0.53  fof(f100,plain,(
% 1.28/0.53    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0))),
% 1.28/0.53    inference(superposition,[],[f90,f24])).
% 1.28/0.53  fof(f24,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f1])).
% 1.28/0.53  fof(f1,axiom,(
% 1.28/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.28/0.53  fof(f90,plain,(
% 1.28/0.53    sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0)),
% 1.28/0.53    inference(superposition,[],[f34,f36])).
% 1.28/0.53  fof(f36,plain,(
% 1.28/0.53    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.28/0.53    inference(resolution,[],[f32,f20])).
% 1.28/0.53  fof(f20,plain,(
% 1.28/0.53    r1_tarski(sK0,sK1)),
% 1.28/0.53    inference(cnf_transformation,[],[f16])).
% 1.28/0.53  fof(f16,plain,(
% 1.28/0.53    ~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 1.28/0.53  fof(f15,plain,(
% 1.28/0.53    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f13,plain,(
% 1.28/0.53    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 1.28/0.53    inference(flattening,[],[f12])).
% 1.28/0.53  fof(f12,plain,(
% 1.28/0.53    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r2_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 1.28/0.53    inference(ennf_transformation,[],[f10])).
% 1.28/0.53  fof(f10,negated_conjecture,(
% 1.28/0.53    ~! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 1.28/0.53    inference(negated_conjecture,[],[f9])).
% 1.28/0.53  fof(f9,conjecture,(
% 1.28/0.53    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).
% 1.28/0.53  fof(f32,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.28/0.53    inference(cnf_transformation,[],[f19])).
% 1.28/0.53  fof(f19,plain,(
% 1.28/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.28/0.53    inference(nnf_transformation,[],[f4])).
% 1.28/0.53  fof(f4,axiom,(
% 1.28/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.28/0.53  fof(f34,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.28/0.53    inference(definition_unfolding,[],[f27,f26])).
% 1.28/0.53  fof(f26,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f7])).
% 1.28/0.53  fof(f7,axiom,(
% 1.28/0.53    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.28/0.53  fof(f27,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.28/0.53    inference(cnf_transformation,[],[f8])).
% 1.28/0.53  fof(f8,axiom,(
% 1.28/0.53    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.28/0.53  fof(f233,plain,(
% 1.28/0.53    k2_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,sK0) | ~spl3_2),
% 1.28/0.53    inference(backward_demodulation,[],[f48,f67])).
% 1.28/0.53  fof(f67,plain,(
% 1.28/0.53    sK0 = sK2 | ~spl3_2),
% 1.28/0.53    inference(avatar_component_clause,[],[f65])).
% 1.28/0.53  fof(f65,plain,(
% 1.28/0.53    spl3_2 <=> sK0 = sK2),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.28/0.53  fof(f48,plain,(
% 1.28/0.53    k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK2)),
% 1.28/0.53    inference(forward_demodulation,[],[f46,f24])).
% 1.28/0.53  fof(f46,plain,(
% 1.28/0.53    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0)),
% 1.28/0.53    inference(superposition,[],[f25,f41])).
% 1.28/0.53  fof(f41,plain,(
% 1.28/0.53    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 1.28/0.53    inference(resolution,[],[f37,f21])).
% 1.28/0.53  fof(f21,plain,(
% 1.28/0.53    r2_xboole_0(sK1,sK2)),
% 1.28/0.53    inference(cnf_transformation,[],[f16])).
% 1.28/0.53  fof(f37,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.28/0.53    inference(resolution,[],[f32,f28])).
% 1.28/0.53  fof(f28,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f18,plain,(
% 1.28/0.53    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.28/0.53    inference(flattening,[],[f17])).
% 1.28/0.53  fof(f17,plain,(
% 1.28/0.53    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.28/0.53    inference(nnf_transformation,[],[f2])).
% 1.28/0.53  fof(f2,axiom,(
% 1.28/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.28/0.53  fof(f218,plain,(
% 1.28/0.53    sK1 = k2_xboole_0(sK0,sK1)),
% 1.28/0.53    inference(backward_demodulation,[],[f49,f206])).
% 1.28/0.53  fof(f206,plain,(
% 1.28/0.53    sK1 = k2_xboole_0(k1_xboole_0,sK1)),
% 1.28/0.53    inference(superposition,[],[f178,f41])).
% 1.28/0.53  fof(f178,plain,(
% 1.28/0.53    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 1.28/0.53    inference(superposition,[],[f92,f25])).
% 1.28/0.53  fof(f92,plain,(
% 1.28/0.53    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) )),
% 1.28/0.53    inference(superposition,[],[f34,f24])).
% 1.28/0.53  fof(f49,plain,(
% 1.28/0.53    k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK0,sK1)),
% 1.28/0.53    inference(superposition,[],[f47,f24])).
% 1.28/0.53  fof(f47,plain,(
% 1.28/0.53    k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1)),
% 1.28/0.53    inference(forward_demodulation,[],[f45,f24])).
% 1.28/0.53  fof(f45,plain,(
% 1.28/0.53    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 1.28/0.53    inference(superposition,[],[f25,f36])).
% 1.28/0.53  fof(f229,plain,(
% 1.28/0.53    r2_xboole_0(sK1,sK0) | ~spl3_2),
% 1.28/0.53    inference(backward_demodulation,[],[f21,f67])).
% 1.28/0.53  fof(f228,plain,(
% 1.28/0.53    spl3_1),
% 1.28/0.53    inference(avatar_contradiction_clause,[],[f225])).
% 1.28/0.53  fof(f225,plain,(
% 1.28/0.53    $false | spl3_1),
% 1.28/0.53    inference(resolution,[],[f219,f43])).
% 1.28/0.53  fof(f43,plain,(
% 1.28/0.53    r1_tarski(sK1,sK2)),
% 1.28/0.53    inference(trivial_inequality_removal,[],[f42])).
% 1.28/0.53  fof(f42,plain,(
% 1.28/0.53    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK2)),
% 1.28/0.53    inference(superposition,[],[f31,f41])).
% 1.28/0.53  fof(f31,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f19])).
% 1.28/0.53  fof(f219,plain,(
% 1.28/0.53    ~r1_tarski(sK1,sK2) | spl3_1),
% 1.28/0.53    inference(backward_demodulation,[],[f73,f206])).
% 1.28/0.53  fof(f73,plain,(
% 1.28/0.53    ~r1_tarski(k2_xboole_0(k1_xboole_0,sK1),sK2) | spl3_1),
% 1.28/0.53    inference(superposition,[],[f69,f49])).
% 1.28/0.53  fof(f69,plain,(
% 1.28/0.53    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),sK2)) ) | spl3_1),
% 1.28/0.53    inference(resolution,[],[f63,f33])).
% 1.28/0.53  fof(f33,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f14])).
% 1.28/0.53  fof(f14,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.28/0.53    inference(ennf_transformation,[],[f5])).
% 1.28/0.53  fof(f5,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.28/0.53  fof(f63,plain,(
% 1.28/0.53    ~r1_tarski(sK0,sK2) | spl3_1),
% 1.28/0.53    inference(avatar_component_clause,[],[f61])).
% 1.28/0.53  fof(f61,plain,(
% 1.28/0.53    spl3_1 <=> r1_tarski(sK0,sK2)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.28/0.53  fof(f68,plain,(
% 1.28/0.53    ~spl3_1 | spl3_2),
% 1.28/0.53    inference(avatar_split_clause,[],[f57,f65,f61])).
% 1.28/0.53  fof(f57,plain,(
% 1.28/0.53    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 1.28/0.53    inference(resolution,[],[f30,f22])).
% 1.28/0.53  fof(f22,plain,(
% 1.28/0.53    ~r2_xboole_0(sK0,sK2)),
% 1.28/0.53    inference(cnf_transformation,[],[f16])).
% 1.28/0.53  fof(f30,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  % SZS output end Proof for theBenchmark
% 1.28/0.53  % (25266)------------------------------
% 1.28/0.53  % (25266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (25266)Termination reason: Refutation
% 1.28/0.53  
% 1.28/0.53  % (25266)Memory used [KB]: 6268
% 1.28/0.53  % (25266)Time elapsed: 0.125 s
% 1.28/0.53  % (25266)------------------------------
% 1.28/0.53  % (25266)------------------------------
% 1.28/0.53  % (25253)Success in time 0.17 s
%------------------------------------------------------------------------------
