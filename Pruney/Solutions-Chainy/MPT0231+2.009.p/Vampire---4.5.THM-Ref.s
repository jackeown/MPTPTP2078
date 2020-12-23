%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 237 expanded)
%              Number of leaves         :    7 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :   74 ( 529 expanded)
%              Number of equality atoms :   44 ( 309 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f28,f124])).

fof(f124,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(subsumption_resolution,[],[f123,f122])).

fof(f122,plain,(
    r1_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f106,f100])).

fof(f100,plain,(
    ! [X1] : sK0 = X1 ),
    inference(subsumption_resolution,[],[f91,f44])).

fof(f44,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f91,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_xboole_0,k1_tarski(X1))
      | sK0 = X1 ) ),
    inference(superposition,[],[f34,f83])).

fof(f83,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f79,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(X0)) ),
    inference(resolution,[],[f33,f44])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f79,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    inference(superposition,[],[f76,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f76,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(superposition,[],[f49,f68])).

fof(f68,plain,(
    k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f65,f28])).

fof(f65,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK0 = sK2 ),
    inference(resolution,[],[f60,f34])).

fof(f60,plain,
    ( r1_tarski(k1_tarski(sK0),k1_tarski(sK2))
    | k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(superposition,[],[f30,f55])).

fof(f55,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f49,plain,(
    ! [X2,X3] : k1_tarski(X2) = k3_xboole_0(k1_tarski(X2),k2_tarski(X2,X3)) ),
    inference(resolution,[],[f33,f30])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

% (7840)Refutation not found, incomplete strategy% (7840)------------------------------
% (7840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7840)Termination reason: Refutation not found, incomplete strategy

% (7840)Memory used [KB]: 1791
% (7840)Time elapsed: 0.106 s
% (7840)------------------------------
% (7840)------------------------------
fof(f106,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),sK0) ),
    inference(backward_demodulation,[],[f30,f100])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,sK0)
      | X0 = X1 ) ),
    inference(forward_demodulation,[],[f109,f100])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(backward_demodulation,[],[f34,f100])).

fof(f28,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:31:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (7843)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (7859)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (7843)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (7840)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (7836)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (7841)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f28,f124])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 = X1) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f123,f122])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    r1_tarski(sK0,sK0)),
% 0.22/0.53    inference(forward_demodulation,[],[f106,f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X1] : (sK0 = X1) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f91,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.53    inference(flattening,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ( ! [X1] : (~r1_tarski(k1_xboole_0,k1_tarski(X1)) | sK0 = X1) )),
% 0.22/0.53    inference(superposition,[],[f34,f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    k1_xboole_0 = k1_tarski(sK0)),
% 0.22/0.53    inference(forward_demodulation,[],[f79,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(X0))) )),
% 0.22/0.53    inference(resolution,[],[f33,f44])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    k1_tarski(sK0) = k3_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 0.22/0.53    inference(superposition,[],[f76,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 0.22/0.53    inference(superposition,[],[f49,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f65,f28])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    k1_xboole_0 = k2_tarski(sK0,sK1) | sK0 = sK2),
% 0.22/0.53    inference(resolution,[],[f60,f34])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    r1_tarski(k1_tarski(sK0),k1_tarski(sK2)) | k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.22/0.53    inference(superposition,[],[f30,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.22/0.53    inference(resolution,[],[f35,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.22/0.53    inference(negated_conjecture,[],[f15])).
% 0.22/0.53  fof(f15,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X2,X3] : (k1_tarski(X2) = k3_xboole_0(k1_tarski(X2),k2_tarski(X2,X3))) )),
% 0.22/0.53    inference(resolution,[],[f33,f30])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).
% 0.22/0.53  % (7840)Refutation not found, incomplete strategy% (7840)------------------------------
% 0.22/0.53  % (7840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7840)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7840)Memory used [KB]: 1791
% 0.22/0.53  % (7840)Time elapsed: 0.106 s
% 0.22/0.53  % (7840)------------------------------
% 0.22/0.53  % (7840)------------------------------
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_tarski(X0),sK0)) )),
% 0.22/0.53    inference(backward_demodulation,[],[f30,f100])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(sK0,sK0) | X0 = X1) )),
% 0.22/0.53    inference(forward_demodulation,[],[f109,f100])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(sK0,k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.53    inference(backward_demodulation,[],[f34,f100])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    sK0 != sK2),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (7843)------------------------------
% 0.22/0.53  % (7843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7843)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (7843)Memory used [KB]: 1791
% 0.22/0.53  % (7843)Time elapsed: 0.105 s
% 0.22/0.53  % (7843)------------------------------
% 0.22/0.53  % (7843)------------------------------
% 0.22/0.53  % (7838)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (7834)Success in time 0.165 s
%------------------------------------------------------------------------------
