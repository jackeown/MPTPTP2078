%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  53 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  82 expanded)
%              Number of equality atoms :   31 (  63 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(subsumption_resolution,[],[f29,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k1_enumset1(X0,X0,X2) = k1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(global_subsumption,[],[f22,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X0,X2) = k1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_relat_1(X4) = k1_enumset1(X0,X0,X2)
      | k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(definition_unfolding,[],[f18,f15,f15])).

fof(f15,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_relat_1(X4) = k2_tarski(X0,X2)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_relat_1(X4) = k2_tarski(X1,X3)
          & k1_relat_1(X4) = k2_tarski(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(definition_unfolding,[],[f17,f15])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f29,plain,(
    k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) ),
    inference(backward_demodulation,[],[f21,f28])).

fof(f21,plain,(
    k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f13,f20,f20,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f20,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f14,f15])).

fof(f14,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f13,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))
   => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:28:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (19787)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (19795)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (19787)Refutation not found, incomplete strategy% (19787)------------------------------
% 0.21/0.52  % (19787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19795)Refutation not found, incomplete strategy% (19795)------------------------------
% 0.21/0.52  % (19795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19787)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19787)Memory used [KB]: 6140
% 0.21/0.52  % (19795)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  % (19787)Time elapsed: 0.004 s
% 0.21/0.52  
% 0.21/0.52  % (19787)------------------------------
% 0.21/0.52  % (19787)------------------------------
% 0.21/0.52  % (19795)Memory used [KB]: 1663
% 0.21/0.52  % (19795)Time elapsed: 0.063 s
% 0.21/0.52  % (19795)------------------------------
% 0.21/0.52  % (19795)------------------------------
% 0.21/0.52  % (19775)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (19779)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (19775)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f29,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X0,X2) = k1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.52    inference(global_subsumption,[],[f22,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X0,X2) = k1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k1_relat_1(X4) = k1_enumset1(X0,X0,X2) | k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f18,f15,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k1_relat_1(X4) = k2_tarski(X0,X2) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : ((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : (((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4) | ~v1_relat_1(X4))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : (v1_relat_1(X4) => (k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4 => (k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (v1_relat_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f17,f15])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))),
% 0.21/0.52    inference(backward_demodulation,[],[f21,f28])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),
% 0.21/0.52    inference(definition_unfolding,[],[f13,f20,f20,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f14,f15])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (19775)------------------------------
% 0.21/0.52  % (19775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19775)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (19775)Memory used [KB]: 10618
% 0.21/0.52  % (19775)Time elapsed: 0.106 s
% 0.21/0.52  % (19775)------------------------------
% 0.21/0.52  % (19775)------------------------------
% 0.21/0.53  % (19771)Success in time 0.161 s
%------------------------------------------------------------------------------
