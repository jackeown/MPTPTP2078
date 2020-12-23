%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:17 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 205 expanded)
%              Number of leaves         :   10 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          :   90 ( 337 expanded)
%              Number of equality atoms :   58 ( 262 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(subsumption_resolution,[],[f192,f15])).

fof(f15,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f192,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f191,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f191,plain,
    ( k1_xboole_0 = sK1
    | sK1 = sK2 ),
    inference(trivial_inequality_removal,[],[f190])).

fof(f190,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | sK1 = sK2 ),
    inference(superposition,[],[f173,f135])).

fof(f135,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f62,f133])).

fof(f133,plain,(
    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f132,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f132,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f44,f124])).

fof(f124,plain,(
    r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f117,f40])).

fof(f40,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f14,f39,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f20,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f37])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f14,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f117,plain,(
    ! [X4,X3] : r1_tarski(X3,k3_tarski(k2_enumset1(X4,X4,X4,X3))) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X4,X3] :
      ( r1_tarski(X3,k3_tarski(k2_enumset1(X4,X4,X4,X3)))
      | r1_tarski(X3,k3_tarski(k2_enumset1(X4,X4,X4,X3))) ) ),
    inference(resolution,[],[f64,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_tarski(k2_enumset1(X2,X2,X2,X0)))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f53,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f25,f39,f39])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f62,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f41,f40])).

fof(f41,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f19,f38])).

fof(f19,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f173,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_xboole_0(X0,sK2)
      | k1_xboole_0 = X0
      | sK2 = X0 ) ),
    inference(resolution,[],[f148,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f148,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | sK2 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f44,f133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:20:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.19/0.52  % (32005)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.19/0.52  % (32009)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.19/0.53  % (31998)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.19/0.53  % (32012)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.19/0.53  % (32012)Refutation not found, incomplete strategy% (32012)------------------------------
% 1.19/0.53  % (32012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (32012)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.53  
% 1.19/0.53  % (32012)Memory used [KB]: 6140
% 1.19/0.53  % (32012)Time elapsed: 0.003 s
% 1.19/0.53  % (32012)------------------------------
% 1.19/0.53  % (32012)------------------------------
% 1.19/0.53  % (32003)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.53  % (32003)Refutation found. Thanks to Tanya!
% 1.36/0.53  % SZS status Theorem for theBenchmark
% 1.36/0.53  % SZS output start Proof for theBenchmark
% 1.36/0.53  fof(f193,plain,(
% 1.36/0.53    $false),
% 1.36/0.53    inference(subsumption_resolution,[],[f192,f15])).
% 1.36/0.53  fof(f15,plain,(
% 1.36/0.53    sK1 != sK2),
% 1.36/0.53    inference(cnf_transformation,[],[f12])).
% 1.36/0.53  fof(f12,plain,(
% 1.36/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.36/0.53    inference(ennf_transformation,[],[f11])).
% 1.36/0.53  fof(f11,negated_conjecture,(
% 1.36/0.53    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.36/0.53    inference(negated_conjecture,[],[f10])).
% 1.36/0.53  fof(f10,conjecture,(
% 1.36/0.53    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.36/0.53  fof(f192,plain,(
% 1.36/0.53    sK1 = sK2),
% 1.36/0.53    inference(subsumption_resolution,[],[f191,f16])).
% 1.36/0.53  fof(f16,plain,(
% 1.36/0.53    k1_xboole_0 != sK1),
% 1.36/0.53    inference(cnf_transformation,[],[f12])).
% 1.36/0.53  fof(f191,plain,(
% 1.36/0.53    k1_xboole_0 = sK1 | sK1 = sK2),
% 1.36/0.53    inference(trivial_inequality_removal,[],[f190])).
% 1.36/0.53  fof(f190,plain,(
% 1.36/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | sK1 = sK2),
% 1.36/0.53    inference(superposition,[],[f173,f135])).
% 1.36/0.53  fof(f135,plain,(
% 1.36/0.53    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 1.36/0.53    inference(backward_demodulation,[],[f62,f133])).
% 1.36/0.53  fof(f133,plain,(
% 1.36/0.53    sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.36/0.53    inference(subsumption_resolution,[],[f132,f17])).
% 1.36/0.53  fof(f17,plain,(
% 1.36/0.53    k1_xboole_0 != sK2),
% 1.36/0.53    inference(cnf_transformation,[],[f12])).
% 1.36/0.53  fof(f132,plain,(
% 1.36/0.53    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 = sK2),
% 1.36/0.53    inference(resolution,[],[f44,f124])).
% 1.36/0.53  fof(f124,plain,(
% 1.36/0.53    r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.36/0.53    inference(superposition,[],[f117,f40])).
% 1.36/0.53  fof(f40,plain,(
% 1.36/0.53    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.36/0.53    inference(definition_unfolding,[],[f14,f39,f38])).
% 1.36/0.53  fof(f38,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.36/0.53    inference(definition_unfolding,[],[f20,f37])).
% 1.36/0.53  fof(f37,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.36/0.53    inference(definition_unfolding,[],[f21,f30])).
% 1.36/0.53  fof(f30,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f7])).
% 1.36/0.53  fof(f7,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.36/0.53  fof(f21,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f6])).
% 1.36/0.53  fof(f6,axiom,(
% 1.36/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.53  fof(f20,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f9])).
% 1.36/0.53  fof(f9,axiom,(
% 1.36/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.36/0.53  fof(f39,plain,(
% 1.36/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.36/0.53    inference(definition_unfolding,[],[f18,f37])).
% 1.36/0.54  fof(f18,plain,(
% 1.36/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f5])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.36/0.54  fof(f14,plain,(
% 1.36/0.54    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.36/0.54    inference(cnf_transformation,[],[f12])).
% 1.36/0.54  fof(f117,plain,(
% 1.36/0.54    ( ! [X4,X3] : (r1_tarski(X3,k3_tarski(k2_enumset1(X4,X4,X4,X3)))) )),
% 1.36/0.54    inference(duplicate_literal_removal,[],[f112])).
% 1.36/0.54  fof(f112,plain,(
% 1.36/0.54    ( ! [X4,X3] : (r1_tarski(X3,k3_tarski(k2_enumset1(X4,X4,X4,X3))) | r1_tarski(X3,k3_tarski(k2_enumset1(X4,X4,X4,X3)))) )),
% 1.36/0.54    inference(resolution,[],[f64,f24])).
% 1.36/0.54  fof(f24,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f13])).
% 1.36/0.54  fof(f13,plain,(
% 1.36/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f1])).
% 1.36/0.54  fof(f1,axiom,(
% 1.36/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.36/0.54  fof(f64,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1),k3_tarski(k2_enumset1(X2,X2,X2,X0))) | r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(resolution,[],[f53,f23])).
% 1.36/0.54  fof(f23,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f13])).
% 1.36/0.54  fof(f53,plain,(
% 1.36/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.36/0.54    inference(equality_resolution,[],[f45])).
% 1.36/0.54  fof(f45,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 1.36/0.54    inference(definition_unfolding,[],[f36,f38])).
% 1.36/0.54  fof(f36,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.36/0.54    inference(cnf_transformation,[],[f2])).
% 1.36/0.54  fof(f2,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.36/0.54  fof(f44,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.36/0.54    inference(definition_unfolding,[],[f25,f39,f39])).
% 1.36/0.54  fof(f25,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f8])).
% 1.36/0.54  fof(f8,axiom,(
% 1.36/0.54    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.36/0.54  fof(f62,plain,(
% 1.36/0.54    k1_xboole_0 = k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.36/0.54    inference(superposition,[],[f41,f40])).
% 1.36/0.54  fof(f41,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.36/0.54    inference(definition_unfolding,[],[f19,f38])).
% 1.36/0.54  fof(f19,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.36/0.54  fof(f173,plain,(
% 1.36/0.54    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(X0,sK2) | k1_xboole_0 = X0 | sK2 = X0) )),
% 1.36/0.54    inference(resolution,[],[f148,f29])).
% 1.36/0.54  fof(f29,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f3])).
% 1.36/0.54  fof(f3,axiom,(
% 1.36/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.36/0.54  fof(f148,plain,(
% 1.36/0.54    ( ! [X0] : (~r1_tarski(X0,sK2) | sK2 = X0 | k1_xboole_0 = X0) )),
% 1.36/0.54    inference(superposition,[],[f44,f133])).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (32003)------------------------------
% 1.36/0.54  % (32003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (32003)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (32003)Memory used [KB]: 6396
% 1.36/0.54  % (32003)Time elapsed: 0.049 s
% 1.36/0.54  % (32003)------------------------------
% 1.36/0.54  % (32003)------------------------------
% 1.36/0.54  % (31991)Success in time 0.171 s
%------------------------------------------------------------------------------
