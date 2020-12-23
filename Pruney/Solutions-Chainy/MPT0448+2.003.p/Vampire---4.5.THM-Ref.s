%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   30 (  43 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  71 expanded)
%              Number of equality atoms :   35 (  48 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42,plain,(
    $false ),
    inference(subsumption_resolution,[],[f17,f41])).

fof(f41,plain,(
    ! [X4,X5] : k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_tarski(X4,X5) ),
    inference(forward_demodulation,[],[f40,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f40,plain,(
    ! [X4,X5] : k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_tarski(X4),k1_tarski(X5)) ),
    inference(forward_demodulation,[],[f39,f31])).

fof(f31,plain,(
    ! [X0,X1] : k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(subsumption_resolution,[],[f28,f30])).

fof(f30,plain,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(superposition,[],[f26,f18])).

fof(f18,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k1_relat_1(X2)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(f39,plain,(
    ! [X4,X5] : k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X4,X5))),k1_tarski(X5)) ),
    inference(forward_demodulation,[],[f38,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_tarski(X1) = k2_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(subsumption_resolution,[],[f27,f30])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(k1_tarski(k4_tarski(X0,X1)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(X2)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X4,X5] : k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X4,X5))),k2_relat_1(k1_tarski(k4_tarski(X4,X5)))) ),
    inference(resolution,[],[f19,f30])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f17,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))
   => k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.36  % Computer   : n025.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % WCLimit    : 600
% 0.13/0.36  % DateTime   : Tue Dec  1 15:24:05 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.51  % (23802)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (23794)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (23802)Refutation not found, incomplete strategy% (23802)------------------------------
% 0.22/0.51  % (23802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23802)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (23802)Memory used [KB]: 1663
% 0.22/0.51  % (23802)Time elapsed: 0.048 s
% 0.22/0.51  % (23802)------------------------------
% 0.22/0.51  % (23802)------------------------------
% 0.22/0.51  % (23794)Refutation not found, incomplete strategy% (23794)------------------------------
% 0.22/0.51  % (23794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23794)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (23794)Memory used [KB]: 6140
% 0.22/0.52  % (23794)Time elapsed: 0.004 s
% 0.22/0.52  % (23794)------------------------------
% 0.22/0.52  % (23794)------------------------------
% 0.22/0.52  % (23786)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (23786)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f17,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X4,X5] : (k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_tarski(X4,X5)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f40,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X4,X5] : (k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_tarski(X4),k1_tarski(X5))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f39,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f28,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 0.22/0.52    inference(superposition,[],[f26,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1))) | ~v1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 0.22/0.52    inference(equality_resolution,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_tarski(X0) = k1_relat_1(X2) | k1_tarski(k4_tarski(X0,X1)) != X2 | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2)) | k1_tarski(k4_tarski(X0,X1)) != X2 | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2)) | k1_tarski(k4_tarski(X0,X1)) != X2) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X4,X5] : (k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X4,X5))),k1_tarski(X5))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f38,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f27,f30])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(k1_tarski(k4_tarski(X0,X1))) | ~v1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 0.22/0.52    inference(equality_resolution,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_tarski(X1) = k2_relat_1(X2) | k1_tarski(k4_tarski(X0,X1)) != X2 | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X4,X5] : (k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X4,X5))),k2_relat_1(k1_tarski(k4_tarski(X4,X5))))) )),
% 0.22/0.52    inference(resolution,[],[f19,f30])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) => k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f9])).
% 0.22/0.52  fof(f9,conjecture,(
% 0.22/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relat_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (23786)------------------------------
% 0.22/0.52  % (23786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23786)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (23786)Memory used [KB]: 6140
% 0.22/0.52  % (23786)Time elapsed: 0.062 s
% 0.22/0.52  % (23786)------------------------------
% 0.22/0.52  % (23786)------------------------------
% 0.22/0.52  % (23778)Success in time 0.146 s
%------------------------------------------------------------------------------
