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
% DateTime   : Thu Dec  3 12:51:28 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   42 (  66 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 ( 123 expanded)
%              Number of equality atoms :   42 (  67 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f127])).

fof(f127,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f75,f113])).

fof(f113,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) ),
    inference(backward_demodulation,[],[f65,f112])).

fof(f112,plain,(
    ! [X0] : k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f72,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f23])).

% (23663)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f23,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

% (23667)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k6_subset_1(k1_relat_1(X0),X1)) = k6_subset_1(X0,k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f41,f46])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

fof(f65,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) ),
    inference(resolution,[],[f35,f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

fof(f75,plain,(
    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f28,f70])).

fof(f70,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[],[f44,f69])).

fof(f69,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f45,f27])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f44,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f33,f29,f29,f42])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f28,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 18:11:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 1.36/0.56  % (23674)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.36/0.56  % (23659)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.36/0.56  % (23658)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.36/0.56  % (23666)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.36/0.56  % (23672)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.36/0.57  % (23674)Refutation not found, incomplete strategy% (23674)------------------------------
% 1.36/0.57  % (23674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (23672)Refutation not found, incomplete strategy% (23672)------------------------------
% 1.36/0.57  % (23672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (23672)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.57  
% 1.36/0.57  % (23672)Memory used [KB]: 1791
% 1.36/0.57  % (23672)Time elapsed: 0.126 s
% 1.36/0.57  % (23672)------------------------------
% 1.36/0.57  % (23672)------------------------------
% 1.56/0.57  % (23664)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.57  % (23674)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (23674)Memory used [KB]: 10618
% 1.56/0.57  % (23674)Time elapsed: 0.134 s
% 1.56/0.57  % (23674)------------------------------
% 1.56/0.57  % (23674)------------------------------
% 1.56/0.57  % (23662)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.56/0.57  % (23660)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.56/0.58  % (23673)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.56/0.58  % (23661)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.56/0.58  % (23664)Refutation found. Thanks to Tanya!
% 1.56/0.58  % SZS status Theorem for theBenchmark
% 1.56/0.58  % (23682)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.56/0.58  % (23681)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.56/0.58  % (23665)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.56/0.58  % (23680)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.56/0.58  % (23685)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.56/0.58  % SZS output start Proof for theBenchmark
% 1.56/0.58  fof(f131,plain,(
% 1.56/0.58    $false),
% 1.56/0.58    inference(trivial_inequality_removal,[],[f127])).
% 1.56/0.58  fof(f127,plain,(
% 1.56/0.58    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 1.56/0.58    inference(superposition,[],[f75,f113])).
% 1.56/0.58  fof(f113,plain,(
% 1.56/0.58    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0)))) )),
% 1.56/0.58    inference(backward_demodulation,[],[f65,f112])).
% 1.56/0.58  fof(f112,plain,(
% 1.56/0.58    ( ! [X0] : (k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0))) )),
% 1.56/0.58    inference(resolution,[],[f72,f27])).
% 1.56/0.58  fof(f27,plain,(
% 1.56/0.58    v1_relat_1(sK1)),
% 1.56/0.58    inference(cnf_transformation,[],[f24])).
% 1.56/0.58  fof(f24,plain,(
% 1.56/0.58    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 1.56/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f23])).
% 1.56/0.58  % (23663)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.56/0.58  fof(f23,plain,(
% 1.56/0.58    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 1.56/0.58    introduced(choice_axiom,[])).
% 1.56/0.58  fof(f14,plain,(
% 1.56/0.58    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.56/0.58    inference(ennf_transformation,[],[f13])).
% 1.56/0.58  % (23667)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.56/0.58  fof(f13,negated_conjecture,(
% 1.56/0.58    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 1.56/0.58    inference(negated_conjecture,[],[f12])).
% 1.56/0.58  fof(f12,conjecture,(
% 1.56/0.58    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).
% 1.56/0.58  fof(f72,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,k6_subset_1(k1_relat_1(X0),X1)) = k6_subset_1(X0,k7_relat_1(X0,X1))) )),
% 1.56/0.58    inference(resolution,[],[f41,f46])).
% 1.56/0.58  fof(f46,plain,(
% 1.56/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.56/0.58    inference(equality_resolution,[],[f39])).
% 1.56/0.58  fof(f39,plain,(
% 1.56/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.56/0.58    inference(cnf_transformation,[],[f26])).
% 1.56/0.58  fof(f26,plain,(
% 1.56/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.58    inference(flattening,[],[f25])).
% 1.56/0.58  fof(f25,plain,(
% 1.56/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.58    inference(nnf_transformation,[],[f1])).
% 1.56/0.58  fof(f1,axiom,(
% 1.56/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.58  fof(f41,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f22])).
% 1.56/0.58  fof(f22,plain,(
% 1.56/0.58    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.56/0.58    inference(flattening,[],[f21])).
% 1.56/0.58  fof(f21,plain,(
% 1.56/0.58    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 1.56/0.58    inference(ennf_transformation,[],[f8])).
% 1.56/0.58  fof(f8,axiom,(
% 1.56/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).
% 1.56/0.58  fof(f65,plain,(
% 1.56/0.58    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)))) )),
% 1.56/0.58    inference(resolution,[],[f35,f27])).
% 1.56/0.58  fof(f35,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))) )),
% 1.56/0.58    inference(cnf_transformation,[],[f16])).
% 1.56/0.58  fof(f16,plain,(
% 1.56/0.58    ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1))),
% 1.56/0.58    inference(ennf_transformation,[],[f7])).
% 1.56/0.58  fof(f7,axiom,(
% 1.56/0.58    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).
% 1.56/0.58  fof(f75,plain,(
% 1.56/0.58    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 1.56/0.58    inference(backward_demodulation,[],[f28,f70])).
% 1.56/0.58  fof(f70,plain,(
% 1.56/0.58    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.56/0.58    inference(superposition,[],[f44,f69])).
% 1.56/0.58  fof(f69,plain,(
% 1.56/0.58    ( ! [X0] : (k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.56/0.58    inference(resolution,[],[f45,f27])).
% 1.56/0.58  fof(f45,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 1.56/0.58    inference(definition_unfolding,[],[f34,f42])).
% 1.56/0.58  fof(f42,plain,(
% 1.56/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.56/0.58    inference(definition_unfolding,[],[f30,f31])).
% 1.56/0.58  fof(f31,plain,(
% 1.56/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f4])).
% 1.56/0.58  fof(f4,axiom,(
% 1.56/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.56/0.58  fof(f30,plain,(
% 1.56/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.56/0.58    inference(cnf_transformation,[],[f6])).
% 1.56/0.58  fof(f6,axiom,(
% 1.56/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.56/0.58  fof(f34,plain,(
% 1.56/0.58    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f15])).
% 1.56/0.58  fof(f15,plain,(
% 1.56/0.58    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.56/0.58    inference(ennf_transformation,[],[f9])).
% 1.56/0.58  fof(f9,axiom,(
% 1.56/0.58    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.56/0.58  fof(f44,plain,(
% 1.56/0.58    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 1.56/0.58    inference(definition_unfolding,[],[f33,f29,f29,f42])).
% 1.56/0.58  fof(f29,plain,(
% 1.56/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f5])).
% 1.56/0.58  fof(f5,axiom,(
% 1.56/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.56/0.58  fof(f33,plain,(
% 1.56/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.56/0.58    inference(cnf_transformation,[],[f3])).
% 1.56/0.58  fof(f3,axiom,(
% 1.56/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.56/0.58  fof(f28,plain,(
% 1.56/0.58    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))),
% 1.56/0.58    inference(cnf_transformation,[],[f24])).
% 1.56/0.58  % SZS output end Proof for theBenchmark
% 1.56/0.58  % (23664)------------------------------
% 1.56/0.58  % (23664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (23664)Termination reason: Refutation
% 1.56/0.58  
% 1.56/0.58  % (23664)Memory used [KB]: 10746
% 1.56/0.58  % (23664)Time elapsed: 0.151 s
% 1.56/0.58  % (23664)------------------------------
% 1.56/0.58  % (23664)------------------------------
% 1.56/0.59  % (23657)Success in time 0.205 s
%------------------------------------------------------------------------------
