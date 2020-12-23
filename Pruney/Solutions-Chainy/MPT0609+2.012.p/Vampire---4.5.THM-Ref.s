%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 100 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 185 expanded)
%              Number of equality atoms :   53 (  99 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f102])).

fof(f102,plain,(
    k4_xboole_0(k1_relat_1(sK1),sK0) != k4_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f87,f93])).

fof(f93,plain,(
    ! [X3] : k4_xboole_0(k1_relat_1(sK1),X3) = k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(X3,k1_relat_1(sK1))) ),
    inference(superposition,[],[f65,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f65,plain,(
    ! [X2] : k4_xboole_0(k1_relat_1(sK1),X2) = k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),X2)) ),
    inference(forward_demodulation,[],[f63,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f63,plain,(
    ! [X2] : k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),X2)) = k5_xboole_0(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),X2)) ),
    inference(superposition,[],[f36,f54])).

fof(f54,plain,(
    ! [X0] : k3_xboole_0(k1_relat_1(sK1),X0) = k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f47,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f47,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK1))
      | k3_xboole_0(k1_relat_1(sK1),X1) = X1 ) ),
    inference(forward_demodulation,[],[f42,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0) ),
    inference(resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21])).

fof(f21,plain,
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

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

fof(f42,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK1))
      | k1_relat_1(k7_relat_1(sK1,X1)) = X1 ) ),
    inference(resolution,[],[f25,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f87,plain,(
    k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,k1_relat_1(sK1))) != k4_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f51,f86])).

fof(f86,plain,(
    ! [X2] : k4_xboole_0(k1_relat_1(sK1),X2) = k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,X2))) ),
    inference(backward_demodulation,[],[f48,f84])).

fof(f84,plain,(
    ! [X0] : k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X0)) = k4_xboole_0(sK1,k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f50,f39])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f50,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k1_relat_1(sK1),X3)
      | k7_relat_1(sK1,k4_xboole_0(X3,X4)) = k4_xboole_0(sK1,k7_relat_1(sK1,X4)) ) ),
    inference(forward_demodulation,[],[f49,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f49,plain,(
    ! [X4,X3] :
      ( k6_subset_1(sK1,k7_relat_1(sK1,X4)) = k7_relat_1(sK1,k4_xboole_0(X3,X4))
      | ~ r1_tarski(k1_relat_1(sK1),X3) ) ),
    inference(forward_demodulation,[],[f44,f29])).

fof(f44,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k1_relat_1(sK1),X3)
      | k6_subset_1(sK1,k7_relat_1(sK1,X4)) = k7_relat_1(sK1,k6_subset_1(X3,X4)) ) ),
    inference(resolution,[],[f25,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

fof(f48,plain,(
    ! [X2] : k4_xboole_0(k1_relat_1(sK1),X2) = k1_relat_1(k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X2))) ),
    inference(forward_demodulation,[],[f43,f29])).

fof(f43,plain,(
    ! [X2] : k6_subset_1(k1_relat_1(sK1),X2) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X2))) ),
    inference(resolution,[],[f25,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

fof(f51,plain,(
    k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f46,f29])).

fof(f46,plain,(
    k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f45,f37])).

fof(f45,plain,(
    k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(backward_demodulation,[],[f40,f41])).

fof(f40,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f26,f29])).

fof(f26,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:56:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (15567)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.51  % (15580)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (15557)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (15572)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.51  % (15564)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (15558)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (15564)Refutation not found, incomplete strategy% (15564)------------------------------
% 0.22/0.52  % (15564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15572)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (15564)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15564)Memory used [KB]: 10618
% 0.22/0.52  % (15564)Time elapsed: 0.099 s
% 0.22/0.52  % (15564)------------------------------
% 0.22/0.52  % (15564)------------------------------
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f102])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    k4_xboole_0(k1_relat_1(sK1),sK0) != k4_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.52    inference(superposition,[],[f87,f93])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ( ! [X3] : (k4_xboole_0(k1_relat_1(sK1),X3) = k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(X3,k1_relat_1(sK1)))) )),
% 0.22/0.52    inference(superposition,[],[f65,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X2] : (k4_xboole_0(k1_relat_1(sK1),X2) = k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),X2))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f63,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X2] : (k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),X2)) = k5_xboole_0(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),X2))) )),
% 0.22/0.52    inference(superposition,[],[f36,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0] : (k3_xboole_0(k1_relat_1(sK1),X0) = k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),X0))) )),
% 0.22/0.52    inference(resolution,[],[f47,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK1)) | k3_xboole_0(k1_relat_1(sK1),X1) = X1) )),
% 0.22/0.52    inference(forward_demodulation,[],[f42,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) )),
% 0.22/0.52    inference(resolution,[],[f25,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    v1_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 0.22/0.52    inference(negated_conjecture,[],[f12])).
% 0.22/0.52  fof(f12,conjecture,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK1)) | k1_relat_1(k7_relat_1(sK1,X1)) = X1) )),
% 0.22/0.52    inference(resolution,[],[f25,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,k1_relat_1(sK1))) != k4_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.52    inference(backward_demodulation,[],[f51,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ( ! [X2] : (k4_xboole_0(k1_relat_1(sK1),X2) = k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,X2)))) )),
% 0.22/0.52    inference(backward_demodulation,[],[f48,f84])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ( ! [X0] : (k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X0)) = k4_xboole_0(sK1,k7_relat_1(sK1,X0))) )),
% 0.22/0.52    inference(resolution,[],[f50,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X4,X3] : (~r1_tarski(k1_relat_1(sK1),X3) | k7_relat_1(sK1,k4_xboole_0(X3,X4)) = k4_xboole_0(sK1,k7_relat_1(sK1,X4))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f49,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X4,X3] : (k6_subset_1(sK1,k7_relat_1(sK1,X4)) = k7_relat_1(sK1,k4_xboole_0(X3,X4)) | ~r1_tarski(k1_relat_1(sK1),X3)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f44,f29])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X4,X3] : (~r1_tarski(k1_relat_1(sK1),X3) | k6_subset_1(sK1,k7_relat_1(sK1,X4)) = k7_relat_1(sK1,k6_subset_1(X3,X4))) )),
% 0.22/0.52    inference(resolution,[],[f25,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X2] : (k4_xboole_0(k1_relat_1(sK1),X2) = k1_relat_1(k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X2)))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f43,f29])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X2] : (k6_subset_1(k1_relat_1(sK1),X2) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X2)))) )),
% 0.22/0.52    inference(resolution,[],[f25,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,k1_relat_1(sK1)))),
% 0.22/0.52    inference(superposition,[],[f46,f29])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k3_xboole_0(sK0,k1_relat_1(sK1)))),
% 0.22/0.52    inference(forward_demodulation,[],[f45,f37])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),sK0))),
% 0.22/0.52    inference(backward_demodulation,[],[f40,f41])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0)))),
% 0.22/0.52    inference(forward_demodulation,[],[f26,f29])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (15572)------------------------------
% 0.22/0.52  % (15572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15572)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (15572)Memory used [KB]: 1791
% 0.22/0.52  % (15572)Time elapsed: 0.111 s
% 0.22/0.52  % (15572)------------------------------
% 0.22/0.52  % (15572)------------------------------
% 0.22/0.53  % (15553)Success in time 0.16 s
%------------------------------------------------------------------------------
