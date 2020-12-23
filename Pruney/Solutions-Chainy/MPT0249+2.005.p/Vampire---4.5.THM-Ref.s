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
% DateTime   : Thu Dec  3 12:38:10 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 202 expanded)
%              Number of leaves         :   11 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :   92 ( 343 expanded)
%              Number of equality atoms :   75 ( 313 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(subsumption_resolution,[],[f87,f19])).

fof(f19,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
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

fof(f87,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f86,f80])).

fof(f80,plain,(
    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f78,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f41,f53])).

fof(f53,plain,(
    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f50,f38])).

fof(f38,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f18,f37,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ) ),
    inference(superposition,[],[f22,f42])).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f27,f36])).

fof(f27,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f24,f37,f37])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f86,plain,(
    sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f79,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f41,f63])).

fof(f63,plain,(
    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f58,f38])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) ),
    inference(superposition,[],[f50,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f28,f36,f36])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (11924)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (11908)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (11912)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (11904)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (11904)Refutation not found, incomplete strategy% (11904)------------------------------
% 0.20/0.52  % (11904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11896)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (11904)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (11904)Memory used [KB]: 10618
% 0.20/0.52  % (11904)Time elapsed: 0.108 s
% 0.20/0.52  % (11904)------------------------------
% 0.20/0.52  % (11904)------------------------------
% 0.20/0.52  % (11915)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (11915)Refutation not found, incomplete strategy% (11915)------------------------------
% 0.20/0.52  % (11915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11915)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (11915)Memory used [KB]: 10618
% 0.20/0.52  % (11915)Time elapsed: 0.127 s
% 0.20/0.52  % (11915)------------------------------
% 0.20/0.52  % (11915)------------------------------
% 0.20/0.52  % (11896)Refutation not found, incomplete strategy% (11896)------------------------------
% 0.20/0.52  % (11896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11896)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (11896)Memory used [KB]: 10746
% 0.20/0.52  % (11896)Time elapsed: 0.109 s
% 0.20/0.52  % (11896)------------------------------
% 0.20/0.52  % (11896)------------------------------
% 1.30/0.52  % (11918)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.30/0.52  % (11912)Refutation not found, incomplete strategy% (11912)------------------------------
% 1.30/0.52  % (11912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.52  % (11917)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.30/0.52  % (11912)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.52  
% 1.30/0.52  % (11912)Memory used [KB]: 10618
% 1.30/0.52  % (11912)Time elapsed: 0.115 s
% 1.30/0.52  % (11912)------------------------------
% 1.30/0.52  % (11912)------------------------------
% 1.30/0.52  % (11917)Refutation not found, incomplete strategy% (11917)------------------------------
% 1.30/0.52  % (11917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.52  % (11917)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.52  
% 1.30/0.52  % (11917)Memory used [KB]: 10746
% 1.30/0.52  % (11917)Time elapsed: 0.138 s
% 1.30/0.52  % (11917)------------------------------
% 1.30/0.52  % (11917)------------------------------
% 1.30/0.53  % (11909)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.30/0.53  % (11898)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.30/0.53  % (11899)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.53  % (11898)Refutation not found, incomplete strategy% (11898)------------------------------
% 1.30/0.53  % (11898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (11898)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (11898)Memory used [KB]: 6140
% 1.30/0.53  % (11898)Time elapsed: 0.125 s
% 1.30/0.53  % (11898)------------------------------
% 1.30/0.53  % (11898)------------------------------
% 1.30/0.53  % (11897)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.53  % (11899)Refutation found. Thanks to Tanya!
% 1.30/0.53  % SZS status Theorem for theBenchmark
% 1.30/0.53  % SZS output start Proof for theBenchmark
% 1.30/0.53  fof(f88,plain,(
% 1.30/0.53    $false),
% 1.30/0.53    inference(subsumption_resolution,[],[f87,f19])).
% 1.30/0.53  fof(f19,plain,(
% 1.30/0.53    sK1 != sK2),
% 1.30/0.53    inference(cnf_transformation,[],[f14])).
% 1.30/0.53  fof(f14,plain,(
% 1.30/0.53    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 1.30/0.53  fof(f13,plain,(
% 1.30/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f12,plain,(
% 1.30/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.30/0.53    inference(ennf_transformation,[],[f11])).
% 1.30/0.53  fof(f11,negated_conjecture,(
% 1.30/0.53    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.30/0.53    inference(negated_conjecture,[],[f10])).
% 1.30/0.53  fof(f10,conjecture,(
% 1.30/0.53    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.30/0.53  fof(f87,plain,(
% 1.30/0.53    sK1 = sK2),
% 1.30/0.53    inference(forward_demodulation,[],[f86,f80])).
% 1.30/0.53  fof(f80,plain,(
% 1.30/0.53    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.30/0.53    inference(subsumption_resolution,[],[f78,f20])).
% 1.30/0.53  fof(f20,plain,(
% 1.30/0.53    k1_xboole_0 != sK1),
% 1.30/0.53    inference(cnf_transformation,[],[f14])).
% 1.30/0.53  fof(f78,plain,(
% 1.30/0.53    k1_xboole_0 = sK1 | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.30/0.53    inference(resolution,[],[f41,f53])).
% 1.30/0.53  fof(f53,plain,(
% 1.30/0.53    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.30/0.53    inference(superposition,[],[f50,f38])).
% 1.30/0.53  fof(f38,plain,(
% 1.30/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.30/0.53    inference(definition_unfolding,[],[f18,f37,f36])).
% 1.30/0.53  fof(f36,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.30/0.53    inference(definition_unfolding,[],[f31,f35])).
% 1.30/0.53  fof(f35,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.30/0.53    inference(definition_unfolding,[],[f30,f34])).
% 1.30/0.53  fof(f34,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.30/0.53    inference(definition_unfolding,[],[f32,f33])).
% 1.30/0.53  fof(f33,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f7])).
% 1.30/0.53  fof(f7,axiom,(
% 1.30/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.30/0.53  fof(f32,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f6])).
% 1.30/0.53  fof(f6,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.30/0.53  fof(f30,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f5])).
% 1.30/0.53  fof(f5,axiom,(
% 1.30/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.30/0.53  fof(f31,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f9])).
% 1.30/0.53  fof(f9,axiom,(
% 1.30/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.30/0.53  fof(f37,plain,(
% 1.30/0.53    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.30/0.53    inference(definition_unfolding,[],[f29,f35])).
% 1.30/0.53  fof(f29,plain,(
% 1.30/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f4])).
% 1.30/0.53  fof(f4,axiom,(
% 1.30/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.30/0.53  fof(f18,plain,(
% 1.30/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.30/0.53    inference(cnf_transformation,[],[f14])).
% 1.30/0.53  fof(f50,plain,(
% 1.30/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.30/0.53    inference(trivial_inequality_removal,[],[f49])).
% 1.30/0.53  fof(f49,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.30/0.53    inference(superposition,[],[f22,f42])).
% 1.30/0.53  fof(f42,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.30/0.53    inference(definition_unfolding,[],[f27,f36])).
% 1.30/0.53  fof(f27,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f3])).
% 1.30/0.53  fof(f3,axiom,(
% 1.30/0.53    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.30/0.53  fof(f22,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f15])).
% 1.30/0.53  fof(f15,plain,(
% 1.30/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.30/0.53    inference(nnf_transformation,[],[f2])).
% 1.30/0.53  fof(f2,axiom,(
% 1.30/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.30/0.53  fof(f41,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.30/0.53    inference(definition_unfolding,[],[f24,f37,f37])).
% 1.30/0.53  fof(f24,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f17])).
% 1.30/0.53  fof(f17,plain,(
% 1.30/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.30/0.53    inference(flattening,[],[f16])).
% 1.30/0.53  fof(f16,plain,(
% 1.30/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.30/0.53    inference(nnf_transformation,[],[f8])).
% 1.30/0.53  fof(f8,axiom,(
% 1.30/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.30/0.53  fof(f86,plain,(
% 1.30/0.53    sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.30/0.53    inference(subsumption_resolution,[],[f79,f21])).
% 1.30/0.53  fof(f21,plain,(
% 1.30/0.53    k1_xboole_0 != sK2),
% 1.30/0.53    inference(cnf_transformation,[],[f14])).
% 1.30/0.53  fof(f79,plain,(
% 1.30/0.53    k1_xboole_0 = sK2 | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.30/0.53    inference(resolution,[],[f41,f63])).
% 1.30/0.53  fof(f63,plain,(
% 1.30/0.53    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.30/0.53    inference(superposition,[],[f58,f38])).
% 1.30/0.53  fof(f58,plain,(
% 1.30/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) )),
% 1.30/0.53    inference(superposition,[],[f50,f43])).
% 1.30/0.53  fof(f43,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 1.30/0.53    inference(definition_unfolding,[],[f28,f36,f36])).
% 1.30/0.53  fof(f28,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f1])).
% 1.30/0.53  fof(f1,axiom,(
% 1.30/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.30/0.53  % SZS output end Proof for theBenchmark
% 1.30/0.53  % (11899)------------------------------
% 1.30/0.53  % (11899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (11899)Termination reason: Refutation
% 1.30/0.53  
% 1.30/0.53  % (11899)Memory used [KB]: 6268
% 1.30/0.53  % (11899)Time elapsed: 0.125 s
% 1.30/0.53  % (11899)------------------------------
% 1.30/0.53  % (11899)------------------------------
% 1.30/0.53  % (11895)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.53  % (11888)Success in time 0.174 s
%------------------------------------------------------------------------------
