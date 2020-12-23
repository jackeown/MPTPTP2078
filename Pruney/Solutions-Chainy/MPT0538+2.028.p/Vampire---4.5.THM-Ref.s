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
% DateTime   : Thu Dec  3 12:49:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  55 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :   83 (  85 expanded)
%              Number of equality atoms :   53 (  55 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(subsumption_resolution,[],[f34,f101])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f100,f81])).

fof(f81,plain,(
    ! [X6] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f74,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f74,plain,(
    ! [X6] : k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f46,f57])).

fof(f57,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f42,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f100,plain,(
    ! [X0] : k8_relat_1(X0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),X0)) ),
    inference(resolution,[],[f47,f80])).

fof(f80,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f66,f78])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f56,f77])).

fof(f77,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_tarski(X3),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f73,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

% (8405)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f73,plain,(
    ! [X3] : k4_xboole_0(k1_tarski(X3),k1_tarski(X3)) = k5_xboole_0(k1_tarski(X3),k1_tarski(X3)) ),
    inference(superposition,[],[f46,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f45,f38])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f56,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f66,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_tarski(sK1(k1_xboole_0)) ),
    inference(resolution,[],[f65,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f65,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(resolution,[],[f48,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

fof(f34,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f29])).

fof(f29,plain,
    ( ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)
   => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

% (8399)Refutation not found, incomplete strategy% (8399)------------------------------
% (8399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8399)Termination reason: Refutation not found, incomplete strategy

% (8399)Memory used [KB]: 10618
% (8399)Time elapsed: 0.127 s
% (8399)------------------------------
% (8399)------------------------------
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:32:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (8398)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (8398)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (8406)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (8414)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (8406)Refutation not found, incomplete strategy% (8406)------------------------------
% 0.22/0.53  % (8406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8397)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (8391)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (8406)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8406)Memory used [KB]: 6140
% 0.22/0.54  % (8406)Time elapsed: 0.102 s
% 0.22/0.54  % (8406)------------------------------
% 0.22/0.54  % (8406)------------------------------
% 0.22/0.54  % (8391)Refutation not found, incomplete strategy% (8391)------------------------------
% 0.22/0.54  % (8391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8391)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8391)Memory used [KB]: 1663
% 0.22/0.54  % (8391)Time elapsed: 0.118 s
% 0.22/0.54  % (8391)------------------------------
% 0.22/0.54  % (8391)------------------------------
% 0.22/0.54  % (8399)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f34,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f100,f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X6] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f74,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X6] : (k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6)) )),
% 0.22/0.54    inference(superposition,[],[f46,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.22/0.54    inference(superposition,[],[f42,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X0] : (k8_relat_1(X0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),X0))) )),
% 0.22/0.54    inference(resolution,[],[f47,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    v1_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f66,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.22/0.54    inference(backward_demodulation,[],[f56,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X3),k1_tarski(X3))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f73,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.54  % (8405)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X3] : (k4_xboole_0(k1_tarski(X3),k1_tarski(X3)) = k5_xboole_0(k1_tarski(X3),k1_tarski(X3))) )),
% 0.22/0.54    inference(superposition,[],[f46,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.22/0.54    inference(superposition,[],[f45,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    v1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_tarski(sK1(k1_xboole_0))),
% 0.22/0.54    inference(resolution,[],[f65,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.22/0.54    inference(unused_predicate_definition_removal,[],[f18])).
% 0.22/0.54  fof(f18,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.22/0.54    inference(resolution,[],[f48,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 0.22/0.54    inference(unused_predicate_definition_removal,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.54    inference(ennf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,negated_conjecture,(
% 0.22/0.54    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.54    inference(negated_conjecture,[],[f20])).
% 0.22/0.54  fof(f20,conjecture,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
% 0.22/0.54  % (8399)Refutation not found, incomplete strategy% (8399)------------------------------
% 0.22/0.54  % (8399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8399)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8399)Memory used [KB]: 10618
% 0.22/0.54  % (8399)Time elapsed: 0.127 s
% 0.22/0.54  % (8399)------------------------------
% 0.22/0.54  % (8399)------------------------------
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (8398)------------------------------
% 0.22/0.54  % (8398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8398)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (8398)Memory used [KB]: 6268
% 0.22/0.54  % (8398)Time elapsed: 0.102 s
% 0.22/0.54  % (8398)------------------------------
% 0.22/0.54  % (8398)------------------------------
% 0.22/0.54  % (8390)Success in time 0.172 s
%------------------------------------------------------------------------------
