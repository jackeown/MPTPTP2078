%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:15 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 125 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  114 ( 262 expanded)
%              Number of equality atoms :   10 (  42 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1628,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1622,f24])).

fof(f24,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20])).

fof(f20,plain,
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f1622,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f1615,f1397])).

fof(f1397,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f1083,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1083,plain,(
    ! [X114,X112,X113] :
      ( ~ r2_hidden(X114,k4_xboole_0(X112,X113))
      | ~ r1_xboole_0(k4_xboole_0(X112,X113),X112) ) ),
    inference(superposition,[],[f38,f95])).

fof(f95,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(resolution,[],[f40,f27])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f29])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1615,plain,(
    ! [X0] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),sK0) ),
    inference(superposition,[],[f1610,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f29,f29])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1610,plain,(
    ! [X2] : r1_xboole_0(k4_xboole_0(sK1,X2),sK0) ),
    inference(resolution,[],[f1579,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1579,plain,(
    ! [X0] : r1_xboole_0(sK0,k4_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f1397,f529])).

fof(f529,plain,(
    ! [X9] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X9))),sK0) ),
    inference(resolution,[],[f454,f45])).

fof(f45,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
      | r1_xboole_0(X1,sK0) ) ),
    inference(resolution,[],[f34,f42])).

fof(f42,plain,(
    r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) ),
    inference(resolution,[],[f33,f36])).

fof(f36,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f26,f29])).

fof(f26,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f454,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,sK2))) ),
    inference(forward_demodulation,[],[f448,f37])).

fof(f448,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),sK0)),k4_xboole_0(X0,k4_xboole_0(X0,sK2))) ),
    inference(resolution,[],[f440,f27])).

fof(f440,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(X1,k4_xboole_0(X1,sK2))) ) ),
    inference(resolution,[],[f41,f25])).

fof(f25,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f29,f29])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:44:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (16051)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.44  % (16034)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.44  % (16039)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (16045)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (16041)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (16036)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (16044)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (16037)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (16042)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (16035)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (16043)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (16046)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (16047)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (16040)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (16038)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (16048)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (16050)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (16049)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.85/0.59  % (16046)Refutation found. Thanks to Tanya!
% 1.85/0.59  % SZS status Theorem for theBenchmark
% 1.85/0.59  % SZS output start Proof for theBenchmark
% 1.85/0.59  fof(f1628,plain,(
% 1.85/0.59    $false),
% 1.85/0.59    inference(subsumption_resolution,[],[f1622,f24])).
% 1.85/0.59  fof(f24,plain,(
% 1.85/0.59    ~r1_xboole_0(sK0,sK1)),
% 1.85/0.59    inference(cnf_transformation,[],[f21])).
% 1.85/0.59  fof(f21,plain,(
% 1.85/0.59    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 1.85/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20])).
% 1.85/0.59  fof(f20,plain,(
% 1.85/0.59    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 1.85/0.59    introduced(choice_axiom,[])).
% 1.85/0.59  fof(f12,plain,(
% 1.85/0.59    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 1.85/0.59    inference(ennf_transformation,[],[f10])).
% 1.85/0.59  fof(f10,negated_conjecture,(
% 1.85/0.59    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 1.85/0.59    inference(negated_conjecture,[],[f9])).
% 1.85/0.59  fof(f9,conjecture,(
% 1.85/0.59    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 1.85/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 1.85/0.59  fof(f1622,plain,(
% 1.85/0.59    r1_xboole_0(sK0,sK1)),
% 1.85/0.59    inference(resolution,[],[f1615,f1397])).
% 1.85/0.59  fof(f1397,plain,(
% 1.85/0.59    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) | r1_xboole_0(X0,X1)) )),
% 1.85/0.59    inference(resolution,[],[f1083,f39])).
% 1.85/0.59  fof(f39,plain,(
% 1.85/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.85/0.59    inference(definition_unfolding,[],[f30,f29])).
% 1.85/0.59  fof(f29,plain,(
% 1.85/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.85/0.59    inference(cnf_transformation,[],[f7])).
% 1.85/0.59  fof(f7,axiom,(
% 1.85/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.85/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.85/0.59  fof(f30,plain,(
% 1.85/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.85/0.59    inference(cnf_transformation,[],[f23])).
% 1.85/0.59  fof(f23,plain,(
% 1.85/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.85/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f22])).
% 1.85/0.59  fof(f22,plain,(
% 1.85/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.85/0.59    introduced(choice_axiom,[])).
% 1.85/0.59  fof(f13,plain,(
% 1.85/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.85/0.59    inference(ennf_transformation,[],[f11])).
% 1.85/0.59  fof(f11,plain,(
% 1.85/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.85/0.59    inference(rectify,[],[f3])).
% 1.85/0.59  fof(f3,axiom,(
% 1.85/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.85/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.85/0.59  fof(f1083,plain,(
% 1.85/0.59    ( ! [X114,X112,X113] : (~r2_hidden(X114,k4_xboole_0(X112,X113)) | ~r1_xboole_0(k4_xboole_0(X112,X113),X112)) )),
% 1.85/0.59    inference(superposition,[],[f38,f95])).
% 1.85/0.59  fof(f95,plain,(
% 1.85/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))) )),
% 1.85/0.59    inference(resolution,[],[f40,f27])).
% 1.85/0.59  fof(f27,plain,(
% 1.85/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.85/0.59    inference(cnf_transformation,[],[f6])).
% 1.85/0.59  fof(f6,axiom,(
% 1.85/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.85/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.85/0.59  fof(f40,plain,(
% 1.85/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.85/0.59    inference(definition_unfolding,[],[f32,f29])).
% 1.85/0.59  fof(f32,plain,(
% 1.85/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.85/0.59    inference(cnf_transformation,[],[f14])).
% 1.85/0.59  fof(f14,plain,(
% 1.85/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.85/0.59    inference(ennf_transformation,[],[f5])).
% 1.85/0.59  fof(f5,axiom,(
% 1.85/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.85/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.85/0.59  fof(f38,plain,(
% 1.85/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.85/0.59    inference(definition_unfolding,[],[f31,f29])).
% 1.85/0.59  fof(f31,plain,(
% 1.85/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.85/0.59    inference(cnf_transformation,[],[f23])).
% 1.85/0.59  fof(f1615,plain,(
% 1.85/0.59    ( ! [X0] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),sK0)) )),
% 1.85/0.59    inference(superposition,[],[f1610,f37])).
% 1.85/0.59  fof(f37,plain,(
% 1.85/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.85/0.59    inference(definition_unfolding,[],[f28,f29,f29])).
% 1.85/0.59  fof(f28,plain,(
% 1.85/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.85/0.59    inference(cnf_transformation,[],[f1])).
% 1.85/0.59  fof(f1,axiom,(
% 1.85/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.85/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.85/0.59  fof(f1610,plain,(
% 1.85/0.59    ( ! [X2] : (r1_xboole_0(k4_xboole_0(sK1,X2),sK0)) )),
% 1.85/0.59    inference(resolution,[],[f1579,f33])).
% 1.85/0.59  fof(f33,plain,(
% 1.85/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.85/0.59    inference(cnf_transformation,[],[f15])).
% 1.85/0.59  fof(f15,plain,(
% 1.85/0.59    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.85/0.59    inference(ennf_transformation,[],[f2])).
% 1.85/0.59  fof(f2,axiom,(
% 1.85/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.85/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.85/0.59  fof(f1579,plain,(
% 1.85/0.59    ( ! [X0] : (r1_xboole_0(sK0,k4_xboole_0(sK1,X0))) )),
% 1.85/0.59    inference(resolution,[],[f1397,f529])).
% 1.85/0.59  fof(f529,plain,(
% 1.85/0.59    ( ! [X9] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X9))),sK0)) )),
% 1.85/0.59    inference(resolution,[],[f454,f45])).
% 1.85/0.59  fof(f45,plain,(
% 1.85/0.59    ( ! [X1] : (~r1_tarski(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | r1_xboole_0(X1,sK0)) )),
% 1.85/0.59    inference(resolution,[],[f34,f42])).
% 1.85/0.59  fof(f42,plain,(
% 1.85/0.59    r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)),
% 1.85/0.59    inference(resolution,[],[f33,f36])).
% 1.85/0.59  fof(f36,plain,(
% 1.85/0.59    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 1.85/0.59    inference(definition_unfolding,[],[f26,f29])).
% 1.85/0.59  fof(f26,plain,(
% 1.85/0.59    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 1.85/0.59    inference(cnf_transformation,[],[f21])).
% 1.85/0.59  fof(f34,plain,(
% 1.85/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.85/0.59    inference(cnf_transformation,[],[f17])).
% 1.85/0.59  fof(f17,plain,(
% 1.85/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.85/0.59    inference(flattening,[],[f16])).
% 1.85/0.59  fof(f16,plain,(
% 1.85/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.85/0.59    inference(ennf_transformation,[],[f8])).
% 1.85/0.59  fof(f8,axiom,(
% 1.85/0.59    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.85/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.85/0.59  fof(f454,plain,(
% 1.85/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) )),
% 1.85/0.59    inference(forward_demodulation,[],[f448,f37])).
% 1.85/0.59  fof(f448,plain,(
% 1.85/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),sK0)),k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) )),
% 1.85/0.59    inference(resolution,[],[f440,f27])).
% 1.85/0.59  fof(f440,plain,(
% 1.85/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(X1,k4_xboole_0(X1,sK2)))) )),
% 1.85/0.59    inference(resolution,[],[f41,f25])).
% 1.85/0.59  fof(f25,plain,(
% 1.85/0.59    r1_tarski(sK0,sK2)),
% 1.85/0.59    inference(cnf_transformation,[],[f21])).
% 1.85/0.59  fof(f41,plain,(
% 1.85/0.59    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,X3) | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))) | ~r1_tarski(X0,X1)) )),
% 1.85/0.59    inference(definition_unfolding,[],[f35,f29,f29])).
% 1.85/0.59  fof(f35,plain,(
% 1.85/0.59    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.85/0.59    inference(cnf_transformation,[],[f19])).
% 1.85/0.59  fof(f19,plain,(
% 1.85/0.59    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 1.85/0.59    inference(flattening,[],[f18])).
% 1.85/0.59  fof(f18,plain,(
% 1.85/0.59    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 1.85/0.59    inference(ennf_transformation,[],[f4])).
% 1.85/0.59  fof(f4,axiom,(
% 1.85/0.59    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 1.85/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).
% 1.85/0.59  % SZS output end Proof for theBenchmark
% 1.85/0.59  % (16046)------------------------------
% 1.85/0.59  % (16046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.59  % (16046)Termination reason: Refutation
% 1.85/0.59  
% 1.85/0.59  % (16046)Memory used [KB]: 2686
% 1.85/0.59  % (16046)Time elapsed: 0.177 s
% 1.85/0.59  % (16046)------------------------------
% 1.85/0.59  % (16046)------------------------------
% 1.85/0.59  % (16033)Success in time 0.233 s
%------------------------------------------------------------------------------
