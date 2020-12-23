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
% DateTime   : Thu Dec  3 12:48:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :    9
%              Number of atoms          :   42 (  48 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f38])).

fof(f38,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f13,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f32,f27])).

fof(f27,plain,(
    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f25,f22])).

fof(f22,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f17,f14])).

fof(f14,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f17,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f25,plain,(
    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f19,f21])).

fof(f21,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f15,f14])).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f32,plain,(
    ! [X0] : k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0),X0) ),
    inference(superposition,[],[f31,f14])).

fof(f31,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),k1_xboole_0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_xboole_0),X1) ),
    inference(resolution,[],[f28,f16])).

fof(f16,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k7_relat_1(k6_relat_1(X2),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ) ),
    inference(resolution,[],[f20,f15])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

% (19130)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f13,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:14:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (19133)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.43  % (19136)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (19133)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f38])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    k1_xboole_0 != k1_xboole_0),
% 0.22/0.43    inference(superposition,[],[f13,f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.43    inference(forward_demodulation,[],[f32,f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.43    inference(forward_demodulation,[],[f25,f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.43    inference(superposition,[],[f17,f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))),
% 0.22/0.43    inference(resolution,[],[f19,f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    v1_relat_1(k1_xboole_0)),
% 0.22/0.43    inference(superposition,[],[f15,f14])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X0] : (k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0),X0)) )),
% 0.22/0.43    inference(superposition,[],[f31,f14])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),k1_xboole_0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_xboole_0),X1)) )),
% 0.22/0.43    inference(resolution,[],[f28,f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(k6_relat_1(X2),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)) )),
% 0.22/0.43    inference(resolution,[],[f20,f15])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(flattening,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  % (19130)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)),
% 0.22/0.43    inference(ennf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,negated_conjecture,(
% 0.22/0.43    ~! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.22/0.43    inference(negated_conjecture,[],[f7])).
% 0.22/0.43  fof(f7,conjecture,(
% 0.22/0.43    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (19133)------------------------------
% 0.22/0.43  % (19133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (19133)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (19133)Memory used [KB]: 10490
% 0.22/0.43  % (19133)Time elapsed: 0.006 s
% 0.22/0.43  % (19133)------------------------------
% 0.22/0.43  % (19133)------------------------------
% 0.22/0.44  % (19129)Success in time 0.076 s
%------------------------------------------------------------------------------
