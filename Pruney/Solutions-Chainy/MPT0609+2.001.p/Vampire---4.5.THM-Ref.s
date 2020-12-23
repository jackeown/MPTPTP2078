%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  86 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 156 expanded)
%              Number of equality atoms :   48 (  83 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f109])).

fof(f109,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f52,f91])).

fof(f91,plain,(
    ! [X1] : k6_subset_1(k1_relat_1(sK1),X1) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X1))) ),
    inference(forward_demodulation,[],[f89,f61])).

fof(f61,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[],[f38,f46])).

% (6727)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f46,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) ),
    inference(unit_resulting_resolution,[],[f24,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f31,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

% (6725)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).

fof(f20,plain,
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

fof(f38,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f26,f28])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f89,plain,(
    ! [X1] : k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X1))) = k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X1))) ),
    inference(superposition,[],[f38,f57])).

fof(f57,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0)))) ),
    inference(forward_demodulation,[],[f54,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f54,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f47,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f33,f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f24,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f52,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f25,f51])).

fof(f51,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) ),
    inference(backward_demodulation,[],[f45,f44])).

fof(f44,plain,(
    ! [X0] : k6_subset_1(sK1,k7_relat_1(sK1,X0)) = k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) ),
    inference(unit_resulting_resolution,[],[f41,f24,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

% (6735)Refutation not found, incomplete strategy% (6735)------------------------------
% (6735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6735)Termination reason: Refutation not found, incomplete strategy

% (6735)Memory used [KB]: 1791
% (6735)Time elapsed: 0.055 s
% (6735)------------------------------
% (6735)------------------------------
% (6723)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f41,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f45,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) ),
    inference(unit_resulting_resolution,[],[f24,f32])).

fof(f32,plain,(
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

fof(f25,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (6732)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.50  % (6745)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (6732)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (6743)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.20/0.51  % (6735)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.20/0.51  % (6738)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.20/0.51  % SZS output start Proof for theBenchmark
% 1.20/0.51  fof(f112,plain,(
% 1.20/0.51    $false),
% 1.20/0.51    inference(trivial_inequality_removal,[],[f109])).
% 1.20/0.51  fof(f109,plain,(
% 1.20/0.51    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 1.20/0.51    inference(superposition,[],[f52,f91])).
% 1.20/0.51  fof(f91,plain,(
% 1.20/0.51    ( ! [X1] : (k6_subset_1(k1_relat_1(sK1),X1) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X1)))) )),
% 1.20/0.51    inference(forward_demodulation,[],[f89,f61])).
% 1.20/0.51  fof(f61,plain,(
% 1.20/0.51    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.20/0.51    inference(superposition,[],[f38,f46])).
% 1.20/0.51  % (6727)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.51  fof(f46,plain,(
% 1.20/0.51    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) )),
% 1.20/0.51    inference(unit_resulting_resolution,[],[f24,f39])).
% 1.20/0.51  fof(f39,plain,(
% 1.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 1.20/0.51    inference(definition_unfolding,[],[f31,f28])).
% 1.20/0.51  fof(f28,plain,(
% 1.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.20/0.51    inference(cnf_transformation,[],[f6])).
% 1.20/0.51  fof(f6,axiom,(
% 1.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.20/0.51  fof(f31,plain,(
% 1.20/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f15])).
% 1.20/0.51  fof(f15,plain,(
% 1.20/0.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.20/0.51    inference(ennf_transformation,[],[f10])).
% 1.20/0.51  fof(f10,axiom,(
% 1.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.20/0.51  % (6725)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.20/0.51  fof(f24,plain,(
% 1.20/0.51    v1_relat_1(sK1)),
% 1.20/0.51    inference(cnf_transformation,[],[f21])).
% 1.20/0.51  fof(f21,plain,(
% 1.20/0.51    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 1.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).
% 1.20/0.51  fof(f20,plain,(
% 1.20/0.51    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 1.20/0.51    introduced(choice_axiom,[])).
% 1.20/0.51  fof(f13,plain,(
% 1.20/0.51    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.20/0.51    inference(ennf_transformation,[],[f12])).
% 1.20/0.51  fof(f12,negated_conjecture,(
% 1.20/0.51    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 1.20/0.51    inference(negated_conjecture,[],[f11])).
% 1.20/0.51  fof(f11,conjecture,(
% 1.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).
% 1.20/0.51  fof(f38,plain,(
% 1.20/0.51    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.20/0.51    inference(definition_unfolding,[],[f29,f26,f28])).
% 1.20/0.51  fof(f26,plain,(
% 1.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f5])).
% 1.20/0.51  fof(f5,axiom,(
% 1.20/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.20/0.51  fof(f29,plain,(
% 1.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.20/0.51    inference(cnf_transformation,[],[f2])).
% 1.20/0.51  fof(f2,axiom,(
% 1.20/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.20/0.51  fof(f89,plain,(
% 1.20/0.51    ( ! [X1] : (k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X1))) = k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X1)))) )),
% 1.20/0.51    inference(superposition,[],[f38,f57])).
% 1.20/0.51  fof(f57,plain,(
% 1.20/0.51    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))))) )),
% 1.20/0.51    inference(forward_demodulation,[],[f54,f27])).
% 1.20/0.51  fof(f27,plain,(
% 1.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f4])).
% 1.20/0.51  fof(f4,axiom,(
% 1.20/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.20/0.51  fof(f54,plain,(
% 1.20/0.51    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1)))) )),
% 1.20/0.51    inference(unit_resulting_resolution,[],[f47,f40])).
% 1.20/0.51  fof(f40,plain,(
% 1.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 1.20/0.51    inference(definition_unfolding,[],[f33,f28])).
% 1.20/0.51  fof(f33,plain,(
% 1.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f17])).
% 1.20/0.51  fof(f17,plain,(
% 1.20/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.20/0.51    inference(ennf_transformation,[],[f3])).
% 1.20/0.51  fof(f3,axiom,(
% 1.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.20/0.51  fof(f47,plain,(
% 1.20/0.51    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))) )),
% 1.20/0.51    inference(unit_resulting_resolution,[],[f24,f30])).
% 1.20/0.51  fof(f30,plain,(
% 1.20/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f14])).
% 1.20/0.51  fof(f14,plain,(
% 1.20/0.51    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.20/0.51    inference(ennf_transformation,[],[f9])).
% 1.20/0.51  fof(f9,axiom,(
% 1.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 1.20/0.51  fof(f52,plain,(
% 1.20/0.51    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 1.20/0.51    inference(backward_demodulation,[],[f25,f51])).
% 1.20/0.51  fof(f51,plain,(
% 1.20/0.51    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0)))) )),
% 1.20/0.51    inference(backward_demodulation,[],[f45,f44])).
% 1.20/0.51  fof(f44,plain,(
% 1.20/0.51    ( ! [X0] : (k6_subset_1(sK1,k7_relat_1(sK1,X0)) = k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) )),
% 1.20/0.51    inference(unit_resulting_resolution,[],[f41,f24,f37])).
% 1.20/0.51  fof(f37,plain,(
% 1.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))) )),
% 1.20/0.51    inference(cnf_transformation,[],[f19])).
% 1.20/0.51  fof(f19,plain,(
% 1.20/0.51    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.20/0.51    inference(flattening,[],[f18])).
% 1.20/0.51  fof(f18,plain,(
% 1.20/0.51    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 1.20/0.51    inference(ennf_transformation,[],[f8])).
% 1.20/0.51  fof(f8,axiom,(
% 1.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).
% 1.20/0.51  % (6735)Refutation not found, incomplete strategy% (6735)------------------------------
% 1.20/0.51  % (6735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.51  % (6735)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.51  
% 1.20/0.51  % (6735)Memory used [KB]: 1791
% 1.20/0.51  % (6735)Time elapsed: 0.055 s
% 1.20/0.51  % (6735)------------------------------
% 1.20/0.51  % (6735)------------------------------
% 1.20/0.52  % (6723)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.20/0.52  fof(f41,plain,(
% 1.20/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.20/0.52    inference(equality_resolution,[],[f35])).
% 1.20/0.52  fof(f35,plain,(
% 1.20/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.20/0.52    inference(cnf_transformation,[],[f23])).
% 1.20/0.52  fof(f23,plain,(
% 1.20/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.20/0.52    inference(flattening,[],[f22])).
% 1.20/0.52  fof(f22,plain,(
% 1.20/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.20/0.52    inference(nnf_transformation,[],[f1])).
% 1.20/0.52  fof(f1,axiom,(
% 1.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.20/0.52  fof(f45,plain,(
% 1.20/0.52    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)))) )),
% 1.20/0.52    inference(unit_resulting_resolution,[],[f24,f32])).
% 1.20/0.52  fof(f32,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f16])).
% 1.20/0.52  fof(f16,plain,(
% 1.20/0.52    ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1))),
% 1.20/0.52    inference(ennf_transformation,[],[f7])).
% 1.20/0.52  fof(f7,axiom,(
% 1.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).
% 1.20/0.52  fof(f25,plain,(
% 1.20/0.52    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))),
% 1.20/0.52    inference(cnf_transformation,[],[f21])).
% 1.20/0.52  % SZS output end Proof for theBenchmark
% 1.20/0.52  % (6732)------------------------------
% 1.20/0.52  % (6732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (6732)Termination reason: Refutation
% 1.20/0.52  
% 1.20/0.52  % (6732)Memory used [KB]: 6268
% 1.20/0.52  % (6732)Time elapsed: 0.098 s
% 1.20/0.52  % (6732)------------------------------
% 1.20/0.52  % (6732)------------------------------
% 1.20/0.52  % (6717)Success in time 0.162 s
%------------------------------------------------------------------------------
