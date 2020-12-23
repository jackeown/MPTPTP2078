%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  48 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 (  77 expanded)
%              Number of equality atoms :   43 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(subsumption_resolution,[],[f51,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) ),
    inference(definition_unfolding,[],[f22,f28,f23])).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) ),
    inference(superposition,[],[f37,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k3_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_tarski(X0,X2),k2_tarski(X1,X3))) ),
    inference(forward_demodulation,[],[f45,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(subsumption_resolution,[],[f41,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_relat_1(X4) = k2_tarski(X0,X2)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f16])).

% (17343)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (17341)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (17343)Refutation not found, incomplete strategy% (17343)------------------------------
% (17343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17343)Termination reason: Refutation not found, incomplete strategy

% (17343)Memory used [KB]: 1663
% (17343)Time elapsed: 0.005 s
% (17343)------------------------------
% (17343)------------------------------
% (17341)Refutation not found, incomplete strategy% (17341)------------------------------
% (17341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17341)Termination reason: Refutation not found, incomplete strategy

% (17341)Memory used [KB]: 1663
% (17341)Time elapsed: 0.094 s
% (17341)------------------------------
% (17341)------------------------------
fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_relat_1(X4) = k2_tarski(X1,X3)
          & k1_relat_1(X4) = k2_tarski(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) = k3_tarski(k2_tarski(k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))),k2_tarski(X1,X3))) ),
    inference(forward_demodulation,[],[f44,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(subsumption_resolution,[],[f40,f26])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relat_1(X4) = k2_tarski(X1,X3)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) = k3_tarski(k2_tarski(k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))),k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))))) ),
    inference(resolution,[],[f38,f26])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f21,f28])).

fof(f21,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f37,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f20,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))
   => k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:21:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (17324)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.47  % (17324)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (17349)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f51,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f27,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f22,f28,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)))),
% 0.20/0.47    inference(superposition,[],[f37,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k3_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_tarski(X0,X2),k2_tarski(X1,X3)))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f45,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f41,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.20/0.47    inference(equality_resolution,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k1_relat_1(X4) = k2_tarski(X0,X2) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4] : ((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4))),
% 0.20/0.47    inference(flattening,[],[f16])).
% 0.20/0.47  % (17343)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.48  % (17341)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.48  % (17343)Refutation not found, incomplete strategy% (17343)------------------------------
% 0.20/0.48  % (17343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17343)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (17343)Memory used [KB]: 1663
% 0.20/0.48  % (17343)Time elapsed: 0.005 s
% 0.20/0.48  % (17343)------------------------------
% 0.20/0.48  % (17343)------------------------------
% 0.20/0.48  % (17341)Refutation not found, incomplete strategy% (17341)------------------------------
% 0.20/0.48  % (17341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17341)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (17341)Memory used [KB]: 1663
% 0.20/0.48  % (17341)Time elapsed: 0.094 s
% 0.20/0.48  % (17341)------------------------------
% 0.20/0.48  % (17341)------------------------------
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4) | ~v1_relat_1(X4))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (v1_relat_1(X4) => (k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4 => (k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k3_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) = k3_tarski(k2_tarski(k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))),k2_tarski(X1,X3)))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f44,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f40,f26])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.20/0.48    inference(equality_resolution,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k2_relat_1(X4) = k2_tarski(X1,X3) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k3_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) = k3_tarski(k2_tarski(k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))),k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))))) )),
% 0.20/0.48    inference(resolution,[],[f38,f26])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f21,f28])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    k2_tarski(sK0,sK1) != k3_relat_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))),
% 0.20/0.48    inference(definition_unfolding,[],[f20,f23])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) => k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f12])).
% 0.20/0.48  fof(f12,conjecture,(
% 0.20/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (17324)------------------------------
% 0.20/0.48  % (17324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17324)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (17324)Memory used [KB]: 6140
% 0.20/0.48  % (17324)Time elapsed: 0.096 s
% 0.20/0.48  % (17324)------------------------------
% 0.20/0.48  % (17324)------------------------------
% 0.20/0.48  % (17315)Success in time 0.129 s
%------------------------------------------------------------------------------
