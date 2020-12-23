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
% DateTime   : Thu Dec  3 12:30:47 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 177 expanded)
%              Number of leaves         :    9 (  51 expanded)
%              Depth                    :   20
%              Number of atoms          :   80 ( 380 expanded)
%              Number of equality atoms :   50 ( 228 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(subsumption_resolution,[],[f96,f23])).

fof(f23,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK0 != sK2
    & r1_xboole_0(sK2,sK1)
    & r1_xboole_0(sK0,sK1)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK0 != sK2
      & r1_xboole_0(sK2,sK1)
      & r1_xboole_0(sK0,sK1)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f96,plain,(
    sK0 = sK2 ),
    inference(forward_demodulation,[],[f95,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f95,plain,(
    sK2 = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f94,f25])).

fof(f94,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f91,f75])).

fof(f75,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f36,f70])).

fof(f70,plain,(
    sK2 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f69,f25])).

fof(f69,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f68,f44])).

fof(f44,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f37,f43])).

fof(f43,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f40,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f40,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f30,f20])).

fof(f20,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f22,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f31,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f22,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f65,f25])).

fof(f65,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f34,f57])).

fof(f57,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(resolution,[],[f52,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f52,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f26,f43])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f29,f29])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f36,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f21,f35])).

fof(f21,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f91,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f34,f89])).

fof(f89,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f88,f32])).

fof(f88,plain,(
    r1_tarski(sK2,sK0) ),
    inference(superposition,[],[f26,f70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (24575)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (24575)Refutation not found, incomplete strategy% (24575)------------------------------
% 0.20/0.50  % (24575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24579)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (24575)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24575)Memory used [KB]: 1791
% 0.20/0.51  % (24575)Time elapsed: 0.098 s
% 0.20/0.51  % (24575)------------------------------
% 0.20/0.51  % (24575)------------------------------
% 0.20/0.51  % (24580)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (24591)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (24583)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (24584)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.19/0.51  % (24585)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.19/0.51  % (24583)Refutation found. Thanks to Tanya!
% 1.19/0.51  % SZS status Theorem for theBenchmark
% 1.19/0.51  % (24604)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.19/0.51  % SZS output start Proof for theBenchmark
% 1.19/0.51  fof(f97,plain,(
% 1.19/0.51    $false),
% 1.19/0.51    inference(subsumption_resolution,[],[f96,f23])).
% 1.19/0.51  fof(f23,plain,(
% 1.19/0.51    sK0 != sK2),
% 1.19/0.51    inference(cnf_transformation,[],[f19])).
% 1.19/0.51  fof(f19,plain,(
% 1.19/0.51    sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 1.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).
% 1.19/0.51  fof(f18,plain,(
% 1.19/0.51    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1))),
% 1.19/0.51    introduced(choice_axiom,[])).
% 1.19/0.51  fof(f15,plain,(
% 1.19/0.51    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 1.19/0.51    inference(flattening,[],[f14])).
% 1.19/0.51  fof(f14,plain,(
% 1.19/0.51    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 1.19/0.51    inference(ennf_transformation,[],[f11])).
% 1.19/0.51  fof(f11,negated_conjecture,(
% 1.19/0.51    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 1.19/0.51    inference(negated_conjecture,[],[f10])).
% 1.19/0.51  fof(f10,conjecture,(
% 1.19/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).
% 1.19/0.51  fof(f96,plain,(
% 1.19/0.51    sK0 = sK2),
% 1.19/0.51    inference(forward_demodulation,[],[f95,f25])).
% 1.19/0.51  fof(f25,plain,(
% 1.19/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.19/0.51    inference(cnf_transformation,[],[f7])).
% 1.19/0.51  fof(f7,axiom,(
% 1.19/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.19/0.51  fof(f95,plain,(
% 1.19/0.51    sK2 = k4_xboole_0(sK0,k1_xboole_0)),
% 1.19/0.51    inference(forward_demodulation,[],[f94,f25])).
% 1.19/0.51  fof(f94,plain,(
% 1.19/0.51    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.19/0.51    inference(forward_demodulation,[],[f91,f75])).
% 1.19/0.51  fof(f75,plain,(
% 1.19/0.51    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 1.19/0.51    inference(backward_demodulation,[],[f36,f70])).
% 1.19/0.51  fof(f70,plain,(
% 1.19/0.51    sK2 = k4_xboole_0(sK0,sK1)),
% 1.19/0.51    inference(forward_demodulation,[],[f69,f25])).
% 1.19/0.51  fof(f69,plain,(
% 1.19/0.51    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.19/0.51    inference(forward_demodulation,[],[f68,f44])).
% 1.19/0.51  fof(f44,plain,(
% 1.19/0.51    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 1.19/0.51    inference(backward_demodulation,[],[f37,f43])).
% 1.19/0.51  fof(f43,plain,(
% 1.19/0.51    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,sK1)),
% 1.19/0.51    inference(forward_demodulation,[],[f40,f30])).
% 1.19/0.51  fof(f30,plain,(
% 1.19/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f8])).
% 1.19/0.51  fof(f8,axiom,(
% 1.19/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.19/0.51  fof(f40,plain,(
% 1.19/0.51    k4_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 1.19/0.51    inference(superposition,[],[f30,f20])).
% 1.19/0.51  fof(f20,plain,(
% 1.19/0.51    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 1.19/0.51    inference(cnf_transformation,[],[f19])).
% 1.19/0.51  fof(f37,plain,(
% 1.19/0.51    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 1.19/0.51    inference(resolution,[],[f22,f35])).
% 1.19/0.51  fof(f35,plain,(
% 1.19/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.19/0.51    inference(definition_unfolding,[],[f31,f29])).
% 1.19/0.51  fof(f29,plain,(
% 1.19/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.19/0.51    inference(cnf_transformation,[],[f9])).
% 1.19/0.51  fof(f9,axiom,(
% 1.19/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.19/0.51  fof(f31,plain,(
% 1.19/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f16])).
% 1.19/0.51  fof(f16,plain,(
% 1.19/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 1.19/0.51    inference(ennf_transformation,[],[f13])).
% 1.19/0.51  fof(f13,plain,(
% 1.19/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.19/0.51    inference(unused_predicate_definition_removal,[],[f3])).
% 1.19/0.51  fof(f3,axiom,(
% 1.19/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.19/0.51  fof(f22,plain,(
% 1.19/0.51    r1_xboole_0(sK2,sK1)),
% 1.19/0.51    inference(cnf_transformation,[],[f19])).
% 1.19/0.51  fof(f68,plain,(
% 1.19/0.51    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 1.19/0.51    inference(forward_demodulation,[],[f65,f25])).
% 1.19/0.52  fof(f65,plain,(
% 1.19/0.52    k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 1.19/0.52    inference(superposition,[],[f34,f57])).
% 1.19/0.52  fof(f57,plain,(
% 1.19/0.52    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 1.19/0.52    inference(resolution,[],[f52,f32])).
% 1.19/0.52  fof(f32,plain,(
% 1.19/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f17])).
% 1.19/0.52  fof(f17,plain,(
% 1.19/0.52    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 1.19/0.52    inference(ennf_transformation,[],[f12])).
% 1.19/0.52  fof(f12,plain,(
% 1.19/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 1.19/0.52    inference(unused_predicate_definition_removal,[],[f4])).
% 1.19/0.52  fof(f4,axiom,(
% 1.19/0.52    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.19/0.52  fof(f52,plain,(
% 1.19/0.52    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 1.19/0.52    inference(superposition,[],[f26,f43])).
% 1.19/0.52  fof(f26,plain,(
% 1.19/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f6])).
% 1.19/0.52  fof(f6,axiom,(
% 1.19/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.19/0.52  fof(f34,plain,(
% 1.19/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.19/0.52    inference(definition_unfolding,[],[f27,f29,f29])).
% 1.19/0.52  fof(f27,plain,(
% 1.19/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.19/0.52    inference(cnf_transformation,[],[f2])).
% 1.19/0.52  fof(f2,axiom,(
% 1.19/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.19/0.52  fof(f36,plain,(
% 1.19/0.52    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.19/0.52    inference(resolution,[],[f21,f35])).
% 1.19/0.52  fof(f21,plain,(
% 1.19/0.52    r1_xboole_0(sK0,sK1)),
% 1.19/0.52    inference(cnf_transformation,[],[f19])).
% 1.19/0.52  fof(f91,plain,(
% 1.19/0.52    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.19/0.52    inference(superposition,[],[f34,f89])).
% 1.19/0.52  fof(f89,plain,(
% 1.19/0.52    k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 1.19/0.52    inference(resolution,[],[f88,f32])).
% 1.19/0.52  fof(f88,plain,(
% 1.19/0.52    r1_tarski(sK2,sK0)),
% 1.19/0.52    inference(superposition,[],[f26,f70])).
% 1.19/0.52  % SZS output end Proof for theBenchmark
% 1.19/0.52  % (24583)------------------------------
% 1.19/0.52  % (24583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (24583)Termination reason: Refutation
% 1.19/0.52  
% 1.19/0.52  % (24583)Memory used [KB]: 10746
% 1.19/0.52  % (24583)Time elapsed: 0.104 s
% 1.19/0.52  % (24583)------------------------------
% 1.19/0.52  % (24583)------------------------------
% 1.19/0.52  % (24578)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.19/0.52  % (24574)Success in time 0.154 s
%------------------------------------------------------------------------------
