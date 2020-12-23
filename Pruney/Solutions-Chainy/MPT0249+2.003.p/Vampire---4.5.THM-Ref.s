%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:10 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   33 (  79 expanded)
%              Number of leaves         :    7 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 208 expanded)
%              Number of equality atoms :   56 ( 184 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(subsumption_resolution,[],[f47,f15])).

fof(f15,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f47,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f46,f42])).

fof(f42,plain,(
    sK1 = k2_tarski(sK0,sK0) ),
    inference(subsumption_resolution,[],[f40,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k2_tarski(sK0,sK0) ),
    inference(resolution,[],[f28,f37])).

fof(f37,plain,(
    r1_tarski(sK1,k2_tarski(sK0,sK0)) ),
    inference(superposition,[],[f29,f25])).

fof(f25,plain,(
    k2_tarski(sK0,sK0) = k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f14,f22,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f14,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X1))
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f18,f22,f22])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f46,plain,(
    sK2 = k2_tarski(sK0,sK0) ),
    inference(subsumption_resolution,[],[f41,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k2_tarski(sK0,sK0) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    r1_tarski(sK2,k2_tarski(sK0,sK0)) ),
    inference(superposition,[],[f32,f25])).

fof(f32,plain,(
    ! [X2,X1] : r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(superposition,[],[f29,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:16:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.14/0.51  % (8044)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.14/0.52  % (8068)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.14/0.52  % (8061)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.14/0.53  % (8053)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.14/0.53  % (8052)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.14/0.53  % (8044)Refutation found. Thanks to Tanya!
% 1.14/0.53  % SZS status Theorem for theBenchmark
% 1.14/0.53  % SZS output start Proof for theBenchmark
% 1.14/0.53  fof(f48,plain,(
% 1.14/0.53    $false),
% 1.14/0.53    inference(subsumption_resolution,[],[f47,f15])).
% 1.14/0.53  fof(f15,plain,(
% 1.14/0.53    sK1 != sK2),
% 1.14/0.53    inference(cnf_transformation,[],[f11])).
% 1.14/0.53  fof(f11,plain,(
% 1.14/0.53    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.14/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).
% 1.14/0.53  fof(f10,plain,(
% 1.14/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.14/0.53    introduced(choice_axiom,[])).
% 1.14/0.53  fof(f9,plain,(
% 1.14/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.14/0.53    inference(ennf_transformation,[],[f8])).
% 1.14/0.53  fof(f8,negated_conjecture,(
% 1.14/0.53    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.14/0.53    inference(negated_conjecture,[],[f7])).
% 1.14/0.53  fof(f7,conjecture,(
% 1.14/0.53    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.14/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.14/0.53  fof(f47,plain,(
% 1.14/0.53    sK1 = sK2),
% 1.14/0.53    inference(forward_demodulation,[],[f46,f42])).
% 1.14/0.53  fof(f42,plain,(
% 1.14/0.53    sK1 = k2_tarski(sK0,sK0)),
% 1.14/0.53    inference(subsumption_resolution,[],[f40,f16])).
% 1.14/0.53  fof(f16,plain,(
% 1.14/0.53    k1_xboole_0 != sK1),
% 1.14/0.53    inference(cnf_transformation,[],[f11])).
% 1.14/0.53  fof(f40,plain,(
% 1.14/0.53    k1_xboole_0 = sK1 | sK1 = k2_tarski(sK0,sK0)),
% 1.14/0.53    inference(resolution,[],[f28,f37])).
% 1.14/0.53  fof(f37,plain,(
% 1.14/0.53    r1_tarski(sK1,k2_tarski(sK0,sK0))),
% 1.14/0.53    inference(superposition,[],[f29,f25])).
% 1.14/0.53  fof(f25,plain,(
% 1.14/0.53    k2_tarski(sK0,sK0) = k3_tarski(k2_tarski(sK1,sK2))),
% 1.14/0.53    inference(definition_unfolding,[],[f14,f22,f23])).
% 1.14/0.53  fof(f23,plain,(
% 1.14/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.14/0.53    inference(cnf_transformation,[],[f6])).
% 1.14/0.53  fof(f6,axiom,(
% 1.14/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.14/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.14/0.53  fof(f22,plain,(
% 1.14/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.14/0.53    inference(cnf_transformation,[],[f3])).
% 1.14/0.53  fof(f3,axiom,(
% 1.14/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.14/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.14/0.53  fof(f14,plain,(
% 1.14/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.14/0.53    inference(cnf_transformation,[],[f11])).
% 1.14/0.53  fof(f29,plain,(
% 1.14/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 1.14/0.53    inference(definition_unfolding,[],[f24,f23])).
% 1.14/0.53  fof(f24,plain,(
% 1.14/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.14/0.53    inference(cnf_transformation,[],[f1])).
% 1.14/0.53  fof(f1,axiom,(
% 1.14/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.14/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.14/0.53  fof(f28,plain,(
% 1.14/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X1)) | k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0) )),
% 1.14/0.53    inference(definition_unfolding,[],[f18,f22,f22])).
% 1.14/0.53  fof(f18,plain,(
% 1.14/0.53    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.14/0.53    inference(cnf_transformation,[],[f13])).
% 1.30/0.53  fof(f13,plain,(
% 1.30/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.30/0.53    inference(flattening,[],[f12])).
% 1.30/0.53  fof(f12,plain,(
% 1.30/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.30/0.53    inference(nnf_transformation,[],[f5])).
% 1.30/0.53  fof(f5,axiom,(
% 1.30/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.30/0.53  fof(f46,plain,(
% 1.30/0.53    sK2 = k2_tarski(sK0,sK0)),
% 1.30/0.53    inference(subsumption_resolution,[],[f41,f17])).
% 1.30/0.53  fof(f17,plain,(
% 1.30/0.53    k1_xboole_0 != sK2),
% 1.30/0.53    inference(cnf_transformation,[],[f11])).
% 1.30/0.53  fof(f41,plain,(
% 1.30/0.53    k1_xboole_0 = sK2 | sK2 = k2_tarski(sK0,sK0)),
% 1.30/0.53    inference(resolution,[],[f28,f36])).
% 1.30/0.53  fof(f36,plain,(
% 1.30/0.53    r1_tarski(sK2,k2_tarski(sK0,sK0))),
% 1.30/0.53    inference(superposition,[],[f32,f25])).
% 1.30/0.53  fof(f32,plain,(
% 1.30/0.53    ( ! [X2,X1] : (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))) )),
% 1.30/0.53    inference(superposition,[],[f29,f21])).
% 1.30/0.53  fof(f21,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f2])).
% 1.30/0.53  fof(f2,axiom,(
% 1.30/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.30/0.53  % SZS output end Proof for theBenchmark
% 1.30/0.53  % (8044)------------------------------
% 1.30/0.53  % (8044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (8044)Termination reason: Refutation
% 1.30/0.53  
% 1.30/0.53  % (8044)Memory used [KB]: 6140
% 1.30/0.53  % (8044)Time elapsed: 0.118 s
% 1.30/0.53  % (8044)------------------------------
% 1.30/0.53  % (8044)------------------------------
% 1.30/0.53  % (8061)Refutation not found, incomplete strategy% (8061)------------------------------
% 1.30/0.53  % (8061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (8036)Success in time 0.162 s
%------------------------------------------------------------------------------
