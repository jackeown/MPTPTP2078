%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:26 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.65s
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
fof(f81,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f64,f78])).

fof(f78,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) ),
    inference(backward_demodulation,[],[f50,f77])).

fof(f77,plain,(
    ! [X0] : k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f75,f41])).

fof(f41,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK1),X0)
      | k6_subset_1(sK1,k7_relat_1(sK1,X1)) = k7_relat_1(sK1,k6_subset_1(X0,X1)) ) ),
    inference(resolution,[],[f35,f22])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

fof(f50,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) ),
    inference(resolution,[],[f31,f22])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

fof(f64,plain,(
    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f23,f60])).

fof(f60,plain,(
    ! [X2] : k6_subset_1(k1_relat_1(sK1),X2) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X2))) ),
    inference(superposition,[],[f39,f55])).

fof(f55,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f40,f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f39,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f29,f24,f24,f36])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f23,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.55  % (22335)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.55/0.56  % (22355)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.55/0.56  % (22354)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.55/0.56  % (22347)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.55/0.57  % (22346)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.55/0.57  % (22354)Refutation found. Thanks to Tanya!
% 1.55/0.57  % SZS status Theorem for theBenchmark
% 1.65/0.57  % (22339)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.65/0.58  % (22337)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.65/0.58  % SZS output start Proof for theBenchmark
% 1.65/0.58  fof(f81,plain,(
% 1.65/0.58    $false),
% 1.65/0.58    inference(trivial_inequality_removal,[],[f80])).
% 1.65/0.58  fof(f80,plain,(
% 1.65/0.58    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 1.65/0.58    inference(superposition,[],[f64,f78])).
% 1.65/0.58  fof(f78,plain,(
% 1.65/0.58    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0)))) )),
% 1.65/0.58    inference(backward_demodulation,[],[f50,f77])).
% 1.65/0.58  fof(f77,plain,(
% 1.65/0.58    ( ! [X0] : (k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0))) )),
% 1.65/0.58    inference(resolution,[],[f75,f41])).
% 1.65/0.58  fof(f41,plain,(
% 1.65/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.65/0.58    inference(equality_resolution,[],[f33])).
% 1.65/0.58  fof(f33,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.65/0.58    inference(cnf_transformation,[],[f21])).
% 1.65/0.58  fof(f21,plain,(
% 1.65/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/0.58    inference(flattening,[],[f20])).
% 1.65/0.58  fof(f20,plain,(
% 1.65/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/0.58    inference(nnf_transformation,[],[f2])).
% 1.65/0.58  fof(f2,axiom,(
% 1.65/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.65/0.58  fof(f75,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK1),X0) | k6_subset_1(sK1,k7_relat_1(sK1,X1)) = k7_relat_1(sK1,k6_subset_1(X0,X1))) )),
% 1.65/0.58    inference(resolution,[],[f35,f22])).
% 1.65/0.58  fof(f22,plain,(
% 1.65/0.58    v1_relat_1(sK1)),
% 1.65/0.58    inference(cnf_transformation,[],[f19])).
% 1.65/0.58  fof(f19,plain,(
% 1.65/0.58    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 1.65/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f18])).
% 1.65/0.58  fof(f18,plain,(
% 1.65/0.58    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 1.65/0.58    introduced(choice_axiom,[])).
% 1.65/0.58  fof(f13,plain,(
% 1.65/0.58    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.65/0.58    inference(ennf_transformation,[],[f12])).
% 1.65/0.58  fof(f12,negated_conjecture,(
% 1.65/0.58    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 1.65/0.58    inference(negated_conjecture,[],[f11])).
% 1.65/0.58  fof(f11,conjecture,(
% 1.65/0.58    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).
% 1.65/0.58  fof(f35,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f17])).
% 1.65/0.58  fof(f17,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.65/0.58    inference(flattening,[],[f16])).
% 1.65/0.58  fof(f16,plain,(
% 1.65/0.58    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 1.65/0.58    inference(ennf_transformation,[],[f9])).
% 1.65/0.58  fof(f9,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).
% 1.65/0.58  fof(f50,plain,(
% 1.65/0.58    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)))) )),
% 1.65/0.58    inference(resolution,[],[f31,f22])).
% 1.65/0.58  fof(f31,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f15])).
% 1.65/0.58  fof(f15,plain,(
% 1.65/0.58    ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1))),
% 1.65/0.58    inference(ennf_transformation,[],[f8])).
% 1.65/0.58  fof(f8,axiom,(
% 1.65/0.58    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).
% 1.65/0.58  fof(f64,plain,(
% 1.65/0.58    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 1.65/0.58    inference(backward_demodulation,[],[f23,f60])).
% 1.65/0.58  fof(f60,plain,(
% 1.65/0.58    ( ! [X2] : (k6_subset_1(k1_relat_1(sK1),X2) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X2)))) )),
% 1.65/0.58    inference(superposition,[],[f39,f55])).
% 1.65/0.58  fof(f55,plain,(
% 1.65/0.58    ( ! [X0] : (k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.65/0.58    inference(resolution,[],[f40,f22])).
% 1.65/0.58  fof(f40,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 1.65/0.58    inference(definition_unfolding,[],[f30,f36])).
% 1.65/0.58  fof(f36,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.65/0.58    inference(definition_unfolding,[],[f26,f27])).
% 1.65/0.58  fof(f27,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f5])).
% 1.65/0.58  fof(f5,axiom,(
% 1.65/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.65/0.58  fof(f26,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f7])).
% 1.65/0.58  fof(f7,axiom,(
% 1.65/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.65/0.58  fof(f30,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f14])).
% 1.65/0.58  fof(f14,plain,(
% 1.65/0.58    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.65/0.58    inference(ennf_transformation,[],[f10])).
% 1.65/0.58  fof(f10,axiom,(
% 1.65/0.58    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.65/0.58  fof(f39,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 1.65/0.58    inference(definition_unfolding,[],[f29,f24,f24,f36])).
% 1.65/0.58  fof(f24,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f6])).
% 1.65/0.58  fof(f6,axiom,(
% 1.65/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.65/0.58  fof(f29,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f4])).
% 1.65/0.58  fof(f4,axiom,(
% 1.65/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.65/0.58  fof(f23,plain,(
% 1.65/0.58    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))),
% 1.65/0.58    inference(cnf_transformation,[],[f19])).
% 1.65/0.58  % SZS output end Proof for theBenchmark
% 1.65/0.58  % (22354)------------------------------
% 1.65/0.58  % (22354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (22354)Termination reason: Refutation
% 1.65/0.58  
% 1.65/0.58  % (22354)Memory used [KB]: 6268
% 1.65/0.58  % (22354)Time elapsed: 0.142 s
% 1.65/0.58  % (22354)------------------------------
% 1.65/0.58  % (22354)------------------------------
% 1.65/0.58  % (22331)Success in time 0.222 s
%------------------------------------------------------------------------------
