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
% DateTime   : Thu Dec  3 12:47:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  55 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :   57 (  83 expanded)
%              Number of equality atoms :   43 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19,f53])).

fof(f53,plain,(
    ! [X4,X5] : k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_tarski(X4,X5) ),
    inference(forward_demodulation,[],[f52,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f41,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(superposition,[],[f26,f20])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f52,plain,(
    ! [X4,X5] : k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_tarski(X4),k1_tarski(X5)) ),
    inference(backward_demodulation,[],[f49,f51])).

fof(f51,plain,(
    ! [X0,X1] : k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(forward_demodulation,[],[f50,f20])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(superposition,[],[f34,f20])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(subsumption_resolution,[],[f32,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_relat_1(X4) = k2_tarski(X0,X2)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_relat_1(X4) = k2_tarski(X1,X3)
          & k1_relat_1(X4) = k2_tarski(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

fof(f49,plain,(
    ! [X4,X5] : k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X4,X5))),k1_tarski(X5)) ),
    inference(backward_demodulation,[],[f38,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X1) ),
    inference(forward_demodulation,[],[f47,f20])).

fof(f47,plain,(
    ! [X0,X1] : k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X1,X1) ),
    inference(superposition,[],[f33,f20])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(subsumption_resolution,[],[f31,f27])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relat_1(X4) = k2_tarski(X1,X3)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X4,X5] : k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X4,X5))),k2_relat_1(k1_tarski(k4_tarski(X4,X5)))) ),
    inference(resolution,[],[f21,f36])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(superposition,[],[f27,f20])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f19,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))
   => k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:15:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (6706)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (6698)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (6698)Refutation not found, incomplete strategy% (6698)------------------------------
% 0.21/0.51  % (6698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6706)Refutation not found, incomplete strategy% (6706)------------------------------
% 0.21/0.51  % (6706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6696)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (6698)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6698)Memory used [KB]: 6140
% 0.21/0.51  % (6698)Time elapsed: 0.005 s
% 0.21/0.51  % (6698)------------------------------
% 0.21/0.51  % (6698)------------------------------
% 0.21/0.51  % (6706)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6706)Memory used [KB]: 1663
% 0.21/0.51  % (6706)Time elapsed: 0.060 s
% 0.21/0.51  % (6706)------------------------------
% 0.21/0.51  % (6706)------------------------------
% 0.21/0.51  % (6690)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (6690)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f19,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X4,X5] : (k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_tarski(X4,X5)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f52,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f41,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.52    inference(superposition,[],[f26,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X4,X5] : (k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_tarski(X4),k1_tarski(X5))) )),
% 0.21/0.52    inference(backward_demodulation,[],[f49,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f50,f20])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 0.21/0.52    inference(superposition,[],[f34,f20])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f32,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k1_relat_1(X4) = k2_tarski(X0,X2) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : ((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : (((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4) | ~v1_relat_1(X4))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : (v1_relat_1(X4) => (k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4 => (k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X4,X5] : (k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X4,X5))),k1_tarski(X5))) )),
% 0.21/0.52    inference(backward_demodulation,[],[f38,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X1)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f47,f20])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X1,X1)) )),
% 0.21/0.52    inference(superposition,[],[f33,f20])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f31,f27])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k2_relat_1(X4) = k2_tarski(X1,X3) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X4,X5] : (k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X4,X5))),k2_relat_1(k1_tarski(k4_tarski(X4,X5))))) )),
% 0.21/0.52    inference(resolution,[],[f21,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 0.21/0.52    inference(superposition,[],[f27,f20])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) => k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 0.21/0.52    inference(negated_conjecture,[],[f11])).
% 0.21/0.52  fof(f11,conjecture,(
% 0.21/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (6690)------------------------------
% 0.21/0.52  % (6690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6690)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (6690)Memory used [KB]: 6268
% 0.21/0.52  % (6690)Time elapsed: 0.074 s
% 0.21/0.52  % (6690)------------------------------
% 0.21/0.52  % (6690)------------------------------
% 0.21/0.52  % (6682)Success in time 0.167 s
%------------------------------------------------------------------------------
